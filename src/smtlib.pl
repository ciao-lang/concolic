% Copyright 2018 Concolic authors
%
% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%     http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.
% ===========================================================================

:- module(_, [], [assertions, fsyntax, dcg]).

:- doc(title, "SMT-LIB printer and parser").

:- doc(module, "This module implements printing and parsing a Prolog
   representation of S-expressions in SMT-LIB syntax (used for
   communication with SMT solvers)").

:- use_module(library(lists), [length/2]).
:- use_module(library(streams)).

% ---------------------------------------------------------------------------
% Write S-expressions to a stream

:- export(wr_es/2).
wr_es([], _S).
wr_es([X|Xs], S) :- wr_e(X, S), nl(S), wr_es(Xs, S).

wr_e(A, _) :- var(A), !, throw(error(unknown(A), wr_e/2)).
wr_e(bitvecval(A,Size), S) :- !,
	( A >= 0 -> A2 = A
	; A < 0 -> A2 is (1<<Size)+A % TODO: better way?
	),
	display(S, '(_ bv'), % (size in text is size in type)
	display(S, A2),
	display(S, ' '),
	display(S, Size),
	display(S, ')').
wr_e(A, S) :- atom(A), !, display(S, A).
wr_e(A, S) :- integer(A), !, display(S, A).
wr_e(vr(N), S) :- !, display(S, 'v!'), display(S, N).
wr_e(sexp(Xs), S) :- !, wr_sexp(Xs,S). % (internal)
wr_e(A, _S) :- !, throw(error(unknown(A), wr_e/2)).

wr_sexp([], S) :- !, display(S,'()').
wr_sexp([X|Xs], S) :- !, display(S,'('), wr_e(X, S), wr_sexp_(Xs, S), display(S,')').

wr_sexp_([], _S).
wr_sexp_([X|Xs], S) :- display(S,' '), wr_e(X, S), wr_sexp_(Xs, S).

% ---------------------------------------------------------------------------
% Read S-expressions from a stream

:- export(rd_e/2).
rd_e(S, X) :-
	current_input(CurIn),
	set_input(S),
	( rd_sexp_codes(Str) ->
	    ps_e(X, Str, [])
	; X = end_of_file % TODO: errors?
	),
	set_input(CurIn).

% Read sexp codes
rd_sexp_codes(Cs) :-
	rd_sexp_codes_(Cs, 0).

rd_sexp_codes_([Ch|Cs], Level) :-
	getct(Ch,_), % (skip layout)
	( Ch = -1 -> fail % EOF
	; rd_sexp_codes1(Ch, Cs, Level)
	).

rd_sexp_codes1(Ch, Cs, Level) :-
	( Ch = 0'( -> Level1 is Level+1, rd_sexp_codes2(Cs, Level1)
	; Ch = 0') -> Level > 0, Level1 is Level-1, rd_sexp_codes3(Cs, Level1)
	; Ch = 0'" -> rd_sexp_string(Cs, Level)
        ; rd_sexp_codes2(Cs, Level)
        ).

rd_sexp_codes2(Cs, Level) :-
	getct(Ch, Type),
	( Type = 0, Level = 0 -> Cs = [] % stop, layout
	; Cs = [Ch|Cs0],
	  rd_sexp_codes1(Ch, Cs0, Level)
        ).

rd_sexp_codes3(Cs, 0) :- !, Cs = []. % (closed)
rd_sexp_codes3(Cs, Level) :- rd_sexp_codes2(Cs, Level).

rd_sexp_string([Ch|Cs], Level) :-
	getct(Ch,_),
	( Ch = 0'" -> rd_sexp_codes2(Cs, Level)
	; Ch = 0'\\ ->
	    getct(Ch2,_),
	    Cs=[Ch2|Cs1], rd_sexp_string(Cs1, Level)
	; rd_sexp_string(Cs, Level)
        ).

% Parse from string
ps_es([X|Xs]) --> ps_e(X), !, ps_es(Xs).
ps_es([]) --> blanks.

ps_e(X) --> blanks, ps_e_(X).

ps_e_(sexp(Xs)) --> "(", !, ps_es(Xs), ")".
ps_e_(X) --> idcodes(Cs), !, { X = ~econs(Cs) }.
ps_e_(X) --> numcodes(Cs), !, { X = ~econs(Cs) }.
ps_e_(string(Cs)) --> "\"", !, ps_str(Cs).

ps_str([]) --> "\"", !.
ps_str([0'\\|Cs]) --> "\\\\", !, ps_str(Cs).
ps_str([0'\"|Cs]) --> "\\\"", !, ps_str(Cs).
ps_str([C|Cs]) --> [C], !, ps_str(Cs).

econs("#x"||Cs) := bitvecval(N, Size) :- !,
	length(Cs, Size),
	number_codes(N, 16, Cs).
econs("v!"||Cs) := vr(Idx) :- !, % (internal)
	number_codes(Idx, Cs).
econs(Cs) := R :-
	atom_codes(R, Cs).

empty([],[]).

ignore_rest(_, []).

numcodes("#x"||Cs) --> "#x", !, numcodes16(Cs).
numcodes([X|Cs]) --> digit(X), !, numcodes_(Cs).

numcodes_([X|Cs]) --> digit(X), !, numcodes_(Cs).
numcodes_("") --> "".

numcodes16([X|Cs]) --> digit16(X), !, numcodes16(Cs).
numcodes16("") --> "".

idcodes([X|Cs]) --> sym(X), !, idcodes_(Cs).
idcodes([X|Cs]) --> alpha(X), !, idcodes_(Cs).

idcodes_([X|Cs]) --> sym(X), !, idcodes_(Cs).
idcodes_([X|Cs]) --> digit(X), !, idcodes_(Cs).
idcodes_([X|Cs]) --> alpha(X), !, idcodes_(Cs).
idcodes_("") --> "".

blanks1 --> blank, blanks.

blanks --> blank, !, blanks.
blanks --> [].

digit(X) --> [X], {X>=0'0, X=<0'9}.

digit16(X) --> [X], {X>=0'0, X=<0'9}, !.
digit16(X) --> [X], {X>=0'a, X=<0'f}, !.
digit16(X) --> [X], {X>=0'A, X=<0'F}.

sym(X) --> [X], { sym_(X) }.

sym_(0'_).
sym_(0'@).
sym_(0'%).
sym_(0'.).
sym_(0'!).
sym_(0'>).
sym_(0'=).
sym_(0'<).
sym_(0'+).
sym_(0'-).
sym_(0'*).
sym_(0'/).

alpha(X) --> [X], { X>=0'a, X=<0'z -> true ; X>=0'A,X=<0'Z -> true ; fail }. 

blank --> [X], { X=<32 }.

