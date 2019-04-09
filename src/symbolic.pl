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

:- doc(title, "Symbolic solver").

:- doc(module, "This module provides support symbolic solving and
   auxiliary definitions for working with symbolic traces. Symbolic
   traces are conjunctions of constraints (for some theories) where
   variables denoting different array states are
   implicit. Satisfiability check and model extraction is optionally
   enhanced with external SMT solvers.").

:- use_module(engine(attributes)).

% ---------------------------------------------------------------------------
:- doc(section, "Flags").

:- data solver_opt/2.

:- export(set_solver_opt/2).
set_solver_opt(Opt, Val) :-
	retractall_fact(solver_opt(Opt, _)),
	assertz_fact(solver_opt(Opt, Val)).

:- export(get_solver_opt/2).
get_solver_opt(Opt, Val) :-
	( solver_opt(Opt, Val0) -> Val = Val0
	; fail
	).

% ---------------------------------------------------------------------------
:- doc(section, "Constraints").

% Dic uses "incomplete" data structures to represent maps with
% symbolic values for keys. Keys must be concrete.
%
% Note: while write operations produce different maps for the
%   changed values, reads must propagate new assignments to previous
%   versions. Example:
%
%   ?- mget(D,x,1), mset(D,y,2,D2), mget(D2,a,3).
%   
%   D = [x=1,a=3|_A],
%   D2 = [x=1,y=2,a=3|_A] ? 
%
% Note: do not use library(dict) since it does not fulfill the
%   property above. Example:
%
%   % ok
%   ?- dic_lookup(D,x,1), dic_replace(D,y,2,D2), dic_lookup(D2,a,3).
%   D = dic(x,1,dic(a,3,_A,_B),_),
%   D2 = dic(x,1,dic(a,3,_A,_B),dic(y,2,_,_)) ? 
%
%   % wrong
%   ?- dic_lookup(D,x,1), dic_replace(D,y,2,D2), dic_lookup(D2,z,3).
%   D = dic(x,1,_A,_),
%   D2 = dic(x,1,_A,dic(y,2,_,dic(z,3,_,_))) ? 

% TODO: The current implementation is O(n) in the size of the map. Use
%   attrvars hiding a difference lists (or other structures) to make
%   it faster.

:- export(map_to_sym/2).
map_to_sym(Xs, Dic) :-
	map_to_sym_(Xs, Ys),
	( get_attribute(Dic, m(Ys0)) -> Ys0 = Ys
	; attach_attribute(Tmp, m(Ys)),
	  Dic = Tmp
	).

map_to_sym_([], _). % (open)
map_to_sym_([K=V|Xs], [K=V|Dic]) :-
	map_to_sym_(Xs, Dic).

:- export(sym_to_map/2).
sym_to_map(Dic) := Xs :-
	( get_attribute(Dic, m(Ys)) -> true
	; attach_attribute(Dic, m(Ys)) % (fresh)
	),
	sym_to_map_(Ys, Xs).

sym_to_map_(Dic, Xs) :- var(Dic), !, Xs = [].
sym_to_map_([K=V|Xs0], [K=V|Xs]) :-
	sym_to_map_(Xs0, Xs).

% :- export(mset/4). % TODO: add constraints when K is symbolic
mset(Dic,K,V) := Dic2 :-
	( get_attribute(Dic, m(Xs)) -> true
	; attach_attribute(Dic, m(Xs)) % (fresh)
	),
	Xs2 = ~mset_(Xs,~concretize(K),V),
	attach_attribute(Tmp, m(Xs2)),
	Dic2 = Tmp.

mset_(Xs,K,V) := [K=V|Xs] :- var(Xs).
mset_([K0=_|Xs],K,V) := [K=V|Xs] :- K0 == K, !.
mset_([K0=V0|Xs],K,V) := [K0=V0| ~mset_(Xs,K,V)].

% :- export(mget/3). % TODO: add constraints when K is symbolic
mget(Dic,K) := ~mget_(Xs,~concretize(K)) :-
	( get_attribute(Dic, m(Xs)) -> true
	; attach_attribute(Dic, m(Xs)) % (fresh)
	).

mget_(Xs,K) := V :- var(Xs), !, Xs=[K=V|_].
mget_([K0=V0|_],K) := V :- K0 == K, !, V = V0.
mget_([_|Xs],K) := ~mget_(Xs,K).

:- export(update/4).
update(Dic,K,V) := Dic2 :-
	trace(sym(update(Dic,K,V,Dic2))),
	Dic2 = ~mset(Dic,K,V).

:- export(element/3).
element(M,N) := Tmp :-
	trace(sym(element(M,N,Tmp))),
	% We need a new variable to keep the trace symbolic
	V = ~mget(M,N),
	Vc = ~concretize(V),
	Tmp = ~newsym(Vc).

% Like update/4 but do not keep track of K % TODO: optimization, needed now?
:- export(update0/4).
update0(Dic,K,V) := Dic2 :-
	trace(sym(update0(Dic,Dic2))),
	Dic2 = ~mset(Dic,K,V).

% Like element/3 but do not keep track of K % TODO: optimization, needed now?
:- export(element0/3).
element0(M,N) := V :-
	V = ~mget(M,N).

% Like element/3 but do not create a temp % TODO: optimization, needed now?
:- export(elementF/3).
elementF(M,N) := V :-
	trace(sym(element(M,N,V))),
	V = ~mget(M,N).

% Xc is the concrete value for X,
% X is preserved as a symbol using attributed variables
ensure(_Ty, X, Xc) :-
	integer(X), !, X = Xc.
ensure(_Ty, X, Xc) :-
	( get_attribute(X, v(Xc0)) -> true
	; attach_attribute(X, v(Xc0))
	),
	Xc = Xc0,
	( integer(Xc) -> true ; ensure_(int64, Xc) ).

% Pick any random value
ensure_(int64, Xc) :- !, Xc = 0.

% Y is a new symbolic variable with value V
newsym(V) := Y :-
	T = _,
	attach_attribute(T, v(V)),
	Y = T.

% Expression is symbolic if it is not a number
is_sym(Xa) :- \+ integer(Xa).

:- export(symtmp/2).
% Create a fresh symbolic variable for the evaluation of X and
% keeps track of the symbolic relation. If X is a concrete value, Tmp
% is unified with it without any symbolic constraint.
symtmp(X) := Y :- is_sym(X), !,
	V = ~concretize(X),
	Y = ~newsym(V), % TODO: delay assignment
	trace(sym(Y=X)).
symtmp(X) := Y :-
	V = ~concretize(X),
	Y = V.

:- export(negcond/2).
negcond(X=Y) := (X\=Y).
negcond(X\=Y) := (X=Y).

:- export(concretize/2).
% Evaluate symbolic expressions, assigning a random value for any
% unassigned symbolic variable.

% TODO: extend
concretize(X) := R :- var(X), !, ensure(int64, X, R0), R = ~to_bv(64, R0).
concretize(N) := R :- integer(N), !, R = ~to_bv(64, N).
concretize(X) := X :- atom(X), !. % (assume a constant)
concretize(+X) := ~concretize(X) :- !.
concretize(-X) := R :- !, R0 is -(~concretize(X)), R = ~to_bv(64, R0).
concretize(X+Y) := R :- !, R0 is ~concretize(X) + ~concretize(Y), R = ~to_bv(64, R0).
concretize(X-Y) := R :- !, R0 is ~concretize(X) - ~concretize(Y), R = ~to_bv(64, R0).
concretize(X*Y) := R :- !, R0 is ~concretize(X) * ~concretize(Y), R = ~to_bv(64, R0).
concretize(X<<Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( Yr > 64 -> R = 0 ; R0 is Xr << Yr, R = ~to_bv(64, R0) ).
concretize(X>>Y) := R :- !, R is ~concretize(X) >> ~concretize(Y).
concretize(ashr(X,Y)) := R :- !, % Like >> but it sets all upper bits to 1 using (-1)<<64 if needed
	R0 is ~signext(64, ~concretize(X)) >> ~concretize(Y),
	R = ~to_bv(64, R0).
concretize(X/\Y) := R :- !, R is ~concretize(X) /\ ~concretize(Y).
concretize(X\/Y) := R :- !, R is ~concretize(X) \/ ~concretize(Y).
concretize(X#Y) := R :- !, R is ~concretize(X) # ~concretize(Y).
concretize(X=Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( Xr = Yr -> R = 1 ; R = 0 ).
concretize(X\=Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( Xr \= Yr -> R = 1 ; R = 0 ).
% unsigned comparison
concretize(uge(X,Y)) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~unsigned(64,Xr) >= ~unsigned(64,Yr) -> R = 1 ; R = 0 ).
concretize(ug(X,Y)) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~unsigned(64,Xr) > ~unsigned(64,Yr) -> R = 1 ; R = 0 ).
concretize(ul(X,Y)) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~unsigned(64,Xr) < ~unsigned(64,Yr) -> R = 1 ; R = 0 ).
concretize(ule(X,Y)) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~unsigned(64,Xr) =< ~unsigned(64,Yr) -> R = 1 ; R = 0 ).
% signed comparison
concretize(X>=Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~signext(64,Xr) >= ~signext(64,Yr) -> R = 1 ; R = 0 ).
concretize(X>Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~signext(64,Xr) > ~signext(64,Yr) -> R = 1 ; R = 0 ).
concretize(X<Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~signext(64,Xr) < ~signext(64,Yr) -> R = 1 ; R = 0 ).
concretize(X=<Y) := R :- !, Xr = ~concretize(X), Yr = ~concretize(Y), ( ~signext(64,Xr) =< ~signext(64,Yr) -> R = 1 ; R = 0 ).
concretize(ite(X,Then,Else)) := R :- !, Xr = ~concretize(X), ( Xr = 1 -> R = ~concretize(Then) ; R = ~concretize(Else) ).
concretize(X) := _ :- throw(error(unknown_solver_expr(X), concretize/2)).

% Use Size-bit mask
to_bv(Size,N) := R :- R is ((1<<Size)-1)/\N.

% Extend sign bit from Size-bit to unbound arithmetic
signext(Size,N) := R :-
	( 0 =:= N /\ (1<<(Size-1)) -> % sign bit is unset
	    R = N
	; SignBits is ((-1)<<Size),
	  R is (N \/ SignBits)
	).

% Unsigned sign bit from Size-bit to unbound arithmetic
unsigned(_,N) := N. % TODO: nothing if the default representation uses to_bv/3

scanlit(element(A,B,C), Dic) --> !, decl(A,Dic,array64), scanexp(B,Dic), scanexp(C,Dic).
scanlit(update(A,B,C,D), Dic) --> !, decl(A,Dic,array64), scanexp(B,Dic), scanexp(C,Dic), decl(D,Dic,array64).
scanlit((A=B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanlit((A\=B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanlit(X, _Dic) --> { throw(unknown(X)) }.

scanexp(A, Dic) --> { var(A) }, !, decl(A, Dic, int64).
scanexp(+A, Dic) --> !, scanexp(A,Dic).
scanexp(-A, Dic) --> !, scanexp(A,Dic).
scanexp(A+B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A-B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A*B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A<<B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A>>B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(ashr(A,B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A/\B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A\/B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A#B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A=B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A\=B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(uge(A,B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(ug(A,B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(ul(A,B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(ule(A,B), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A>=B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A>B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A<B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(A=<B, Dic) --> !, scanexp(A,Dic), scanexp(B,Dic).
scanexp(ite(A,B,C), Dic) --> !, scanexp(A,Dic), scanexp(B,Dic), scanexp(C,Dic).
scanexp(_A, _Dic) --> [].

% ---------------------------------------------------------------------------
:- doc(section, "Derivation trace (both symbolic constraints and custom items)").
%
% Use with_trace/2 to execute a predicate with some local trace and
% add_trace/1 to concatenate elements to that trace.

:- use_module(engine(internals), ['$global_vars_get'/2]). % (reserve 16)

% (very low-level, see mutables.pl implementation for details)
:- use_module(engine(internals), ['$setarg'/4]).
:- import(internals, ['$global_vars_get_root'/1]).

get_trace(X) :-
	'$global_vars_get'(16,tr(X)).

set_trace(X) :-
	'$global_vars_set'(16,tr(X)).

'$global_vars_set'(I, X) :-
        '$global_vars_get_root'(R),
	'$setarg'(I, R, X, on).

% (not significantly faster or slower)
%% :- use_module(engine(attributes)).
%% 
%% get_trace(X) :-
%% 	'$global_vars_get'(16,G),
%% 	( type(G,attv) -> get_attribute(G,tr(X))
%% 	; attach_attribute(G,tr(X))
%% 	).
%% 
%% set_trace(X) :-
%% 	'$global_vars_get'(16,G),
%% 	( type(G,attv) -> detach_attribute(G) ; true ),
%% 	  attach_attribute(G,tr(X)).

:- export(with_trace/2).
:- meta_predicate with_trace(?,goal).
with_trace(Trace, Goal) :-
	get_trace(OldTrace),
	set_trace(Trace), % new fresh trace
	Goal,
	get_trace([]), % close trace
	set_trace(OldTrace).

:- export(drop_trace/1).
:- meta_predicate drop_trace(goal).
drop_trace(Goal) :-
	get_trace(OldTrace),
	set_trace(_),
	Goal,
	set_trace(OldTrace).

:- export(trace/1).
% Add X to the trace
trace(X) :-
	get_trace([X|Trace]), set_trace(Trace).

% ---------------------------------------------------------------------------
:- doc(section, "Solver").

:- export(get_model/2).
get_model(Goal, Status) :-
	prop_array(Goal),
	smt_get_solver(Solver),
	smt_begin(Solver),
	smt_assert(Solver, Goal, RevDic),
	smt_check_sat(Solver, Result),
	( sat_result(Result) -> true
	; throw(error(bad_status(Result), get_model/2))
	),
	Status = Result,
	( Status = sat ->
	    smt_get_model(Solver, RevDic),
	    %% \+ \+ ( numbervars(Model,0,_), format("Goal: ~q~nRevDic: ~q~n", [Goal, RevDic]) ) % (verbose)
	    smt_end(Solver),
	    % TODO: (it may not be needed if we get the arrays directly from SMT)
	    ( assign_arr(Goal) ->
	        true
	    ; % Note: this should not happen
	      throw(error(could_not_reconstruct_model, get_model/1))
	    )
	; true
	).

sat_result(sat).
sat_result(unsat).
sat_result(unknown).

:- export(get_model/1).
get_model(Goal) :-
	get_model(Goal, Status),
	( Status = unsat -> fail
	; Status = unknown -> throw(error(unknown, get_model/1)) % TODO: what should we do?
	; Status = sat -> true
	).

% TODO: Very incomplete... implement real propagation or use a SMT
% propagate some array constraints for registers
prop_array(Goal) :-
	prop_array_(Goal, _).

prop_array_([], _).
prop_array_([element(A,K,V)|Cs], Dic) :- atom(K), var(V), !,
	dic_lookup(Dic,(A,K),V),
	prop_array_(Cs, Dic).
prop_array_([_|Cs], Dic) :-
	prop_array_(Cs, Dic).

assign_arr([]).
assign_arr([C|Cs]) :- !,
	( assign1(C) -> true ; true ), % TODO: may fail due to bitvec vs int!
	assign_arr(Cs).

assign1(element(M,I,V)) :- !, V0 = ~mget(M,I), ( type(V0,var) -> V=V0 ; true ). % TODO: ugly
assign1(update(M0,I,V,M)) :- !, M = ~mset(M0,I,V).
assign1(update0(M0,M)) :- !, M = M0.
assign1(_).

% ---------------------------------------------------------------------------

:- use_module(library(terms_vars)).

:- export(erase_and_dump_constrs/2).
% Remove constraints and obtain its goal representation
% TODO: make it general
erase_and_dump_constrs(X, Goal) :- nonvar(X), X = c(M,A), !,
	M1 = ~sym_to_map(M),
	A1 = ~sym_to_map(A),
	erase_model(c(M,A)),
	init_mem(M1,M,Goal,Goal0),
	init_mem(A1,A,Goal0,[]).
erase_and_dump_constrs(X, []) :- % TODO: incomplete if X contains arrays
	erase_model(X).

init_mem([],_) --> [].
init_mem([K=V|D],Arr) --> [element(Arr,K,V)], init_mem(D,Arr).

:- export(erase_model/1).
% Drop any concrete assignment to symbolic variables on Term
erase_model(Term) :-
	varset(Term, Vars),
	unassign(Vars, _Map).

:- export(unassign/2).
% Unassign concrete values assigned to symbolic variables
% Obtain the assignment in the Map argument.
unassign([], []).
unassign([X|Xs], Map) :-
	( type(X,attv), get_attribute(X, v(V)) ->
	    detach_attribute(X),
	    Map = [X=V|Map0]
	; type(X,attv), get_attribute(X, m(_)) ->
	    detach_attribute(X),
	    Map = Map0
	; Map = Map0
	),
	unassign(Xs, Map0).

% ---------------------------------------------------------------------------
% SMT interface (via SMTLIB format)

% TODO: add other solvers

:- use_module(library(port_reify)).
:- use_module(library(process)).
:- use_module(library(streams), [close/1]).
:- use_module(library(dict)).
:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(system), [file_exists/1, current_executable/1, find_executable/2]).
:- use_module(library(pathnames), [path_concat/3, path_split/3]).

:- use_module(.(smtlib)).

:- use_module(engine(internals), [ciao_root/1]).

% TODO: use Ciao builder 3rd party support
find_bin(Cmd, Path) :-
	% relative to the current executable
	current_executable(ExecPath),
	path_split(ExecPath, Dir, _),
	( Path0 = ~path_concat(Dir, Cmd)
	; Path0 = ~path_concat(~path_concat(Dir, 'third-party/bin'), Cmd)
	; Path0 = ~path_concat(~path_concat(~ciao_root, 'third-party/bin'), Cmd)
	),
	file_exists(Path0),
	!,
	Path = Path0.
find_bin(Cmd, Path) :- % in the PATH
	find_executable(Cmd, Path).

:- data z3_bin_/1.
z3_bin := Path :-
	( z3_bin_(Path0) -> true
	; find_bin('z3', Path0), set_fact(z3_bin_(Path0))
	),
	Path = Path0.

:- data has_smt_/1.
has_smt :- 
	( has_smt_(X) -> true
	; ( file_exists(~z3_bin) -> X = yes
	  ; X = no,
	    message(warning, ['could not detect any external SMT solver'])
	  ),
	  assertz_fact(has_smt_(X))
	),
	X = yes.

% :- use_module(library(format)).
:- use_module(engine(stream_basic), [flush_output/1]).

:- data z3_process/3.

smt_get_solver(Solver) :-
	Solver = solver(PSolver, In, Out),
	( z3_process(PSolver, In, Out) ->
	    true
	; has_smt ->
	    process_call(~z3_bin, ['-in'], [stdin(stream(In)), stdout(stream(Out)), status(_), background(PSolver)]),
	    % message(error, ['starting z3']),
	    assertz_fact(z3_process(PSolver, In, Out))
	; throw(error(no_solver, smt_get_solver/1))
	).

smt_close :-
	z3_process(PSolver, In, Out), !,
	close(In),
	close(Out),
	process_join(PSolver),
	retractall_fact(z3_process(_,_,_)).
smt_close.

% ---------------------------------------------------------------------------

smt_assert(Solver, Goal, RevDic) :-
	Solver = solver(_PSolver, In, _Out),
%	( \+ \+ tell_cmds(user_output, Goal, _) -> true ; true ), % (verbose)
	smt_assert_(In, Goal, RevDic),
	flush_output(In).

% Rewrite goal and tell SMT commands (declarations, assert, check sat, get model, etc.)
smt_assert_(S, Goal0, RevDic) :-
	Goal = ~filter_noreg(Goal0),
	( scangoal(Goal, _Dic, Decls, []) -> true
	; throw(scangoal_failed(Goal))
	),
	namedecls(Decls, 0, RevDic),
	rw_cmds(Decls, Goal, Cmds, []),
	\+ \+ (
	  unifnames(RevDic),
	  wr_es(Cmds, S)).

% Ignore array constraints with constant atomic keys (registers)
% TODO: really ad-hoc, improve
filter_noreg([]) := [].
filter_noreg([X|Xs]) := ~filter_noreg(Xs) :-
	( X = element(_,K,_), atom(K) % a register
	; X = update(_,K,_,_), atom(K) % a register
	; X = update0(_,_)
	),
	!.
filter_noreg([X|Xs]) := [X| ~filter_noreg(Xs)].

% give names to declared variables (assume no repetitions)
namedecls([], _, _).
namedecls([decl(X,_)|Cs], Idx, Dic) :-
	Idx1 is Idx + 1,
	dic_lookup(Dic, Idx, X),
	namedecls(Cs, Idx1, Dic).

% unify vars with its name
unifnames(X) :- var(X), !.
unifnames(dic(Idx,V,L,R)) :-
	V = vr(Idx),
	unifnames(L),
	unifnames(R).

scangoal([], _) --> [].
scangoal([C|Cs], Dic) --> scanlit(C, Dic), scangoal(Cs, Dic).

decl(A, Dic, Type) --> ( { dic_get(Dic, A, _) } -> [] ; { dic_lookup(Dic, A, _) }, [decl(A,Type)] ).

rw_cmds(Decls, Goal) -->
	rw_decls(Decls),
	rw_goal(Goal).

rw_decls([]) --> [].
rw_decls([decl(X,Type)|Ds]) -->
	( { Type = int64 } ->
	    [sexp(['declare-fun',~rw_e(X),sexp([]),'Int64'])]
	; { Type = array64 } ->
	    [sexp(['declare-fun',~rw_e(X),sexp([]),'Array64'])]
	; { fail }
	),
	rw_decls(Ds).

rw_goal([]) --> [].
rw_goal([X|Cs]) --> { Y = ~rw_g(X) }, [Y], rw_goal(Cs).

rw_g(A) := _ :- var(A) , !, throw(unknown_g(A)).
rw_g(A=B) := sexp(['assert',~rw_sexp('=',[A,B])]) :- !.
rw_g(A\=B) := sexp(['assert',sexp(['not',~rw_sexp('=',[A,B])])]) :- !.
rw_g(element(A,B,C)) := sexp(['assert',sexp(['=',~rw_sexp('select',[A,B]), ~rw_e(C)])]) :- !.
rw_g(update(A,B,C,D)) := sexp(['assert',sexp(['=',~rw_sexp('store',[A,B,C]), ~rw_e(D)])]) :- !.
rw_g(A) := _ :- !, throw(unknown_g(A)).

rw_e(A) := R :- var(A), !, R = A. % (note: it should be renamed later)
rw_e(A) := bitvecval(A,64) :- integer(A), !. % TODO: ad-hoc
rw_e(A) := A :- atom(A), !. % TODO: sure?
rw_e(A) := vr(Idx) :- A = vr(Idx), !.
rw_e(-A) := ~rw_sexp('bvneg',[A]) :- !.
rw_e(A+B) := ~rw_sexp('bvadd',[A,B]) :- !.
rw_e(A-B) := ~rw_sexp('bvsub',[A,B]) :- !.
rw_e(A*B) := ~rw_sexp('bvmul',[A,B]) :- !.
rw_e(A<<B) := ~rw_sexp('bvshl',[A,B]) :- !.
rw_e(A>>B) := ~rw_sexp('bvlshr',[A,B]) :- !.
rw_e(ashr(A,B)) := ~rw_sexp('bvashr',[A,B]) :- !.
rw_e(A/\B) := ~rw_sexp('bvand',[A,B]) :- !.
rw_e(A\/B) := ~rw_sexp('bvor',[A,B]) :- !.
rw_e(A#B) := ~rw_sexp('bvxor',[A,B]) :- !.
rw_e(A\=B) := sexp(['ite',~rw_sexp('=',[A,B]),bitvecval(0,64),bitvecval(1,64)]) :- !.
rw_e(A) := sexp(['ite',~rw_p(A),bitvecval(1,64),bitvecval(0,64)]) :- is_p(A), !.
rw_e(ite(A,B,C)) := sexp(['ite',~rw_p(A),~rw_e(B),~rw_e(C)]) :- !. % TODO: make sure that A is boolean
rw_e(A) := _ :- !, throw(error(unknown(A), rw_e/2)).

rw_p(A=B) := ~rw_sexp('=',[A,B]) :- !.
rw_p(A\=B) := sexp([not,~rw_sexp('=',[A,B])]) :- !.
rw_p(uge(A,B)) := ~rw_sexp('bvuge',[A,B]) :- !.
rw_p(ug(A,B)) := ~rw_sexp('bvugt',[A,B]) :- !.
rw_p(ul(A,B)) := ~rw_sexp('bvult',[A,B]) :- !.
rw_p(ule(A,B)) := ~rw_sexp('bvule',[A,B]) :- !.
rw_p(A>=B) := ~rw_sexp('bvsge',[A,B]) :- !.
rw_p(A>B) := ~rw_sexp('bvsgt',[A,B]) :- !.
rw_p(A<B) := ~rw_sexp('bvslt',[A,B]) :- !.
rw_p(A=<B) := ~rw_sexp('bvsle',[A,B]) :- !.
rw_p(A) := ~rw_e(A).

is_p(_=_).
is_p(_\=_).
is_p(uge(_,_)).
is_p(ug(_,_)).
is_p(ul(_,_)).
is_p(ule(_,_)).
is_p(_>=_).
is_p(_<_).
is_p(_>_).
is_p(_=<_).

rw_sexp(F, Xs) := R :- R = sexp([F| ~rw_es(Xs)]).

rw_es([]) := [].
rw_es([X|Xs]) := [~rw_e(X)| ~rw_es(Xs)].

% ---------------------------------------------------------------------------
% Send/receive S-exp to/from the solver

smt_send(solver(_,In,_), Cmds) :-
	wr_es(Cmds, In),
	flush_output(In).

smt_recv(Solver, Answer) :-
	Solver = solver(_PSolver, _In, Out),
	%% format("SMT output: ~s~n", [Out]), % (verbose)
	rd_answer(Out, Answer).

rd_answer(S, X) :-
	( rd_e(S, X0) -> true
	; throw(error(parse, smt_recv/2))
	),
	( X0 = sexp(['error', string(_Str)]) ->
%	    message(warning, ['[smt] ', $$(Str)]),
	    rd_answer(S, X)
	; X = X0
%	  message(error, ['rda: ', X])
	).

% ---------------------------------------------------------------------------

smt_begin(Solver) :-
	rw_begin(Cmds, []),
	smt_send(Solver, Cmds).

rw_begin -->
	[sexp(['reset'])],
	[sexp(['define-sort', 'Int64', sexp([]), sexp(['_', 'BitVec', '64'])])],
	[sexp(['define-sort', 'Array64', sexp([]), sexp(['Array', 'Int64', 'Int64'])])].

% ---------------------------------------------------------------------------

:- compilation_fact(keep_alive).
:- if(defined(keep_alive)).
smt_end(_). % keep alive
:- else.
% % (Exit the solver)
smt_end(Solver) :- smt_send(Solver, [sexp(['exit'])]), smt_close.
:- endif.

% ---------------------------------------------------------------------------

smt_check_sat(Solver, Result) :-
	( get_solver_opt(timeout, TO) ->
	    % (value 0 is treated as no timeout)
	    smt_send(Solver, [sexp(['set-option', ':timeout', TO])])
	; true
	),
	smt_send(Solver, [sexp(['check-sat'])]),
	smt_recv(Solver, Result0),
	( Result0 = unsat -> Result = unsat
	; Result0 = sat -> Result = sat
	; Result0 = unknown -> Result = unknown
	; throw(error(unknown_answer(Result0), smt_check_sat/2))
	).

% ---------------------------------------------------------------------------

smt_get_model(Solver, RevDic) :-
	smt_send(Solver, [sexp(['get-model'])]),
	smt_recv(Solver, Answer),
	( Answer = sexp([model|Model0]) ->
	    Model = ~dump_model(Model0, RevDic)
	; throw(error(unknown_answer(Answer), smt_get_model/2))
	),
	assign_model(Model).

assign_model([X=V|Cs]) :- integer(V), !, X = ~newsym(V), assign_model(Cs).
assign_model([]).

dump_model([sexp(['define-fun', vr(Idx), sexp([]), sexp(['_','BitVec',_]), bitvecval(V,_)])|Xs], RevDic, [X=V|Cs]) :-
	dic_get(RevDic, Idx, X),
	!,
	dump_model(Xs, RevDic, Cs).
dump_model([_|Xs], RevDic, Cs) :- !,
	dump_model(Xs, RevDic, Cs).
dump_model([], _, []).

