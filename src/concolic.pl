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

:- module(_, [], [assertions, fsyntax, datafacts, dcg, hiord]).

:- doc(title, "Concolic search").

:- use_module(library(lists)).
:- use_module(concolic(symbolic)).
:- use_module(engine(runtime_control), [statistics/2]).

:- doc(module, "This module implements a (more or less) generic
   concolic search algorithm. See @pred{conc_call/3} for details.").

:- export(conc_call/3).
% Call goal Goal using a concolic search algorithm. It will provide
% solutions that explore all paths whose constraints are marked as
% 'cond(_)'.
:- meta_predicate conc_call(goal, ?, ?).
conc_call(Goal, InConf, Trace) :-
	reset_saved_sympath,
	( % Initial input
	  first_input(InConf, NegMarks)
	; % Compute next input (nondet until no more inputs can be generated)
	  erase_and_dump_constrs(InConf, InGoal),
	  repeat,
	  ( next_input(InConf, InGoal, NegMarks) -> true
	  ; % No more solutions (cut repeat/0 and fail)
	    !, fail 
	  )
	),
	( with_trace(Trace, Goal) -> true ; fail ), % (only one solution)
	% save sympath
	sym_filter(Trace,SymPath),
	save_sympath(InConf,SymPath,NegMarks).

% Just do nothing (it assumes that execution does "lazy concretization").
first_input(_InConf, []).

:- export(conc_cond/2).
% Choose a condition on a symbolic constraint. V is 1 if it was true or
% 0 if it was false for the current values. The constraint is added to
% the symbolic trace to allow the exploration of other paths.
conc_cond(C) := CondV :- C=(A=B), !,
	Ac = ~concretize(A),
	Bc = ~concretize(B),
	( Ac = Bc -> Cond = C, CondV=1
	; Cond = ~negcond(C), CondV=0
	),
	trace(sym(cond(Cond))).

:- export(conc_stats/3).
% Collect statistics for concolic runs (erased for each new solution)
:- data conc_stats/3.

% Timeout for computing next path (optional)
:- data conc_nextpath_timeout/1.

get_nextpath_timeout := T :-
	( conc_nextpath_timeout(T0) -> T = T0
	; T = 0 % (disabled)
	).

:- export(set_nextpath_timeout/1).
set_nextpath_timeout(T) :-
	set_fact(conc_nextpath_timeout(T)).

% ---------------------------------------------------------------------------
% NOTE: numbervars/3 and melt/2 are a workaround for a limit in the
%   number of free variables in dynamic predicates, and assert items
%   individually. erase_model/1 is needed in any case.
%   

:- use_module(library(write), [numbervars/3]).

%:- data saved_sympath/1.
:- data savedpath/2.

reset_saved_sympath :-
%	retractall_fact(saved_sympath(_)).
	retractall_fact(savedpath(_,_)).

retract_saved_sympath(Xs) :-
%	retract_fact(saved_sympath(Xs0)), % TODO: a single term reach other db limits
	retract_fact(savedpath(inconf, InConf0)),
	retract_saved_sympath_lst(sympath, SymPath0),
	retract_saved_sympath_lst(negmarks, NegMarks0),
        Xs0 = (InConf0,SymPath0,NegMarks0),
	melt(Xs0, Xs).

asserta_saved_sympath(Xs) :-
	\+ \+ (
          erase_model(Xs),
	  numbervars(Xs,1,_),
%	  asserta_fact(saved_sympath(Xs)) % TODO: a single term reach other db limits
	  Xs = (InConf,SymPath,NegMarks),
	  assertz_fact(savedpath(inconf, InConf)),
	  asserta_saved_sympath_lst(sympath, SymPath),
	  asserta_saved_sympath_lst(negmarks, NegMarks)
        ).

retract_saved_sympath_lst(Arg, Xs) :-
	retract_fact(savedpath(Arg, X)), !,
	Xs = [X|Xs0],
	retract_saved_sympath_lst(Arg, Xs0).
retract_saved_sympath_lst(_Arg, []).

asserta_saved_sympath_lst(Arg, Xs) :-
	( member(X, Xs),
	    assertz_fact(savedpath(Arg, X)),
	    fail
	; true
	).

% Negate last condition and find an input model.
% If a model is not found, negate the previous condition and try again.
next_input(InConf, InGoal, NewNegMarks) :-
	retractall_fact(conc_stats(_,_,_)),
	retract_saved_sympath((InConf,SymPath,NegMarks)),
	next_input_(InGoal,SymPath,NegMarks,NewNegMarks).

next_input_(InGoal,SymPath,NegMarks,NewNegMarks) :-
	% TODO: better way to do updatecond?
	( updatecond(SymPath,NegMarks,SymPath1) -> true
	; throw(sympath_mismatch(SymPath,NegMarks))
	),
	( NewSymPath = ~neglastcond(SymPath1) ->
	    NewNegMarks0 = ~only_negmarks(NewSymPath)
	; log('[concolic] finished, no more conditions to negate'), fail
	),
	log('[concolic] negating last path condition and computing new model...'),
	%
	% Find a model that satisfy InGoal and NewSymPath.
        % The new model is implicitly assigned to the symbolic variables.
	length(NewSymPath, SymPathLen), % (for statistics)
	Goal = ~append(InGoal,~pathgoal(NewSymPath)),
	%
	set_solver_opt(timeout, ~get_nextpath_timeout),
	statistics(walltime, [T0, _]),
	get_model(Goal, Status),
	statistics(walltime, [T1, _]), T is T1-T0,
	assertz_fact(conc_stats(SymPathLen,T,Status)),
	( Status = sat ->
	    log('[concolic] new input model found'),
	    NewNegMarks = NewNegMarks0
	; % unknown or unsat
	  log('[concolic] no model found, negate previous condition...'),
	  SymPathPrev = ~removelastcond(SymPath1), % (it should not fail)
	  next_input_(InGoal,SymPathPrev,~only_negmarks(SymPathPrev),NewNegMarks)
	).

only_negmarks([]) := [] :- !.
only_negmarks([cond(_)|Xs]) := [cond| ~only_negmarks(Xs)] :- !.
only_negmarks([_|Xs]) := [other| ~only_negmarks(Xs)].

% Save the symbolic path (without any model assignment)
save_sympath(InConf, SymPath, NegMarks) :-
	asserta_saved_sympath((InConf,SymPath,NegMarks)).

% Update cond/1 conditions in new sympath w.r.t. old sympath to
% preserve "already negated" info (needed to avoid repeating paths)
updatecond(SymPath, [], SymPath) :- !.
updatecond([], _, []) :- !.
updatecond([C|SymPath], [C2|NegMarks], [C3|SynPath2]) :- !,
	updatecond_(C, C2, C3),
	updatecond(SymPath, NegMarks, SynPath2).

updatecond_(cond(C), cond, cond(C)) :- !.
updatecond_(cond(C), other, C) :- !. % already negated
updatecond_(C, _, C) :- !. % other constraint

% Negate last condition (fail if no more conditions)
neglastcond(SymPath) := NSymPath :-
	SymPath1 = ~reverse(SymPath),
	SymPath2 = ~neglastcond_(SymPath1),
	NSymPath = ~reverse(SymPath2).

% cond/1 is removed so that we do not negate it again
neglastcond_([cond(Constr)|SymPath]) := [~negcond(Constr)|SymPath] :- !.
neglastcond_([_|SymPath]) := ~neglastcond_(SymPath) :- !.

% Remove last condition (fail if no more conditions)
removelastcond(SymPath) := NSymPath :-
	SymPath1 = ~reverse(SymPath),
	SymPath2 = ~removelastcond_(SymPath1),
	NSymPath = ~reverse(SymPath2).

removelastcond_([cond(_)|SymPath]) := SymPath :- !.
removelastcond_([_|SymPath]) := ~removelastcond_(SymPath) :- !.

% ---------------------------------------------------------------------------

melt(X,Y) :- melt1(X,Y,_), !.

melt1(X,Y,S) :- X = '$VAR'(_), !, assoc(X,Y,S).
melt1(X,X,_) :- atomic(X), !.
melt1(X,Y,S) :- functor(X,F,N), functor(Y,F,N), meltargs(1,N,X,Y,S).

meltargs(I,N,_,_,_) :- I > N, !.
meltargs(I,N,X,Y,S) :-
	arg(I,X,Xi),
	melt1(Xi,Yi,S),
	arg(I,Y,Yi),
	I1 is I+1,
	meltargs(I1,N,X,Y,S).

assoc(X,Y,[assoc(X,Y)|_]) :- !.
assoc(X,Y,[_|S]) :- assoc(X,Y,S).

variable('$VAR'(_)).	

% ---------------------------------------------------------------------------

:- export(pathgoal/2).
% Goal from a sympath (just remove cond/1)
pathgoal(Cs) := Cs2 :- pathgoal_(Cs, Cs2, []).

pathgoal_([]) --> [].
pathgoal_([cond(C)|Cs]) --> !, pathgoal_([C|Cs]).
pathgoal_([C|Cs]) --> !, [C], pathgoal_(Cs).

:- export(sym_filter/2).
% Get only symbolic constraints from the trace
sym_filter([sym(C)|Trace]) := [C| ~sym_filter(Trace)] :- !.
sym_filter([_|Trace]) := ~sym_filter(Trace).
sym_filter([]) := [].

% ---------------------------------------------------------------------------
% (log messages)

:- use_module(engine(messages_basic), [message/2]).

log(X) :- message(user, X).


