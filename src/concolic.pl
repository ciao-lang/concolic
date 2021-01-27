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

%! \title Concolic search
%
%  \module This module implements a (more or less) generic concolic
%  search algorithm. See @pred{conc_call/3} for details.
%
%  It is based on implicit symbolic traces. Symbolic traces are
%  conjunctions of constraints (for some theories) where variables
%  denoting different array states are implicit. Satisfiability check
%  and model extraction is based on the @lib{ciaosmt} module.

:- use_module(library(terms_vars)).
:- use_module(library(lists)).
:- use_module(concolic(ciaosmt)).
:- use_module(engine(runtime_control), [statistics/2]).

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
      erase_constraints(InConf, InGoal, _),
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

% ---------------------------------------------------------------------------
%! # Derivation trace (both symbolic constraints and custom items)
%
% Use `with_trace/2` to execute a predicate with some local trace and
% `add_trace/1` to concatenate elements to that trace.

:- use_module(engine(internals), ['$global_vars_get'/2, '$global_vars_set'/2]). % (reserve 16)

get_trace(X) :-
    '$global_vars_get'(16,V0),
    ( V0=0 -> % (uninitialized)
        X=[] % (just some default value)
    ; V0=tr(X)
    ).

set_trace(X) :-
    '$global_vars_set'(16,tr(X)).

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
%! # Trace-based constraints

:- export(conc_cond/2).
% Choose a condition on a symbolic constraint. V is 'true' if it was true or
% 'false' if it was false for the current values. The constraint is added to
% the symbolic trace to allow the exploration of other paths.
conc_cond(C) := CondV :-
    concretize(C),
    CondV0 = ~eval(C), % TODO: use true/false instead of 1/0?
    ( CondV0 = 1 -> Cond = C, CondV = true
    ; Cond = ~negbool(C), CondV = false
    ),
    trace(sym(cond(Cond))).

:- export(update/4).
% update(Dic,K,V,Dic2): (requires concretized K)
update(Dic,K,V) := Dic2 :-
    concretize(K),
    trace(sym(update(Dic,K,V,Dic2))),
    Dic2 = ~eval(store(Dic,K,V)).

:- export(element/3).
% element(Dic,K,V): (requires concretized K)
element(Dic,K) := V :-
    concretize(K),
    trace(sym(element(Dic,K,V))),
    V = ~eval(select(Dic,K)).

:- export(assign/2).
% Evaluate X and assign its value to a fresh variable To, keeping track of the
% symbolic relation.
% (requires concretized X)
assign(To, X) :-
    concretize(X),
    trace(sym(To=X)),
    assign_eval(To, X).

:- export(concretize/1).
% Assign default values for all unassigned variables in X expression.
% All variable must have been declared. This ensures that eval/2
% has enough concrete information to evaluate an expression.
concretize(X) :-
    varset(X, Vars),
    concretize_(Vars).

concretize_([]).
concretize_([X|Xs]) :-
    assign_default(X),
    concretize_(Xs).

% ---------------------------------------------------------------------------

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
%   individually. erase_constraints/3 is needed in any case.

:- use_module(library(write), [numbervars/3]).

%:- data saved_sympath/1.
:- data savedpath/2.

reset_saved_sympath :-
%   retractall_fact(saved_sympath(_)).
    retractall_fact(savedpath(_,_)).

retract_saved_sympath(InConf,SymPath,NegMarks) :-
%   retract_fact(saved_sympath(Xs0)), % TODO: a single term reach other db limits
    retract_fact(savedpath(inconf, InConf0)),
    retract_saved_sympath_lst(sympath, SymPath0),
    retract_saved_sympath_lst(negmarks, NegMarks0),
    Xs0 = (InConf0,SymPath0,NegMarks0),
    melt(Xs0, Xs),
    Xs = (InConf,SymPath,NegMarks).

% Save the symbolic path (without any model assignment)
save_sympath(InConf, SymPath, NegMarks) :-
    \+ \+ (
      Xs = (InConf,SymPath,NegMarks),
      erase_constraints(Xs, _, _),
      numbervars(Xs,1,_),
%     asserta_fact(saved_sympath(Xs)) % TODO: a single term reach other db limits
      assertz_fact(savedpath(inconf, InConf)),
      assertz_saved_sympath_lst(sympath, SymPath),
      assertz_saved_sympath_lst(negmarks, NegMarks)
    ).

retract_saved_sympath_lst(Arg, Xs) :-
    retract_fact(savedpath(Arg, X)), !,
    Xs = [X|Xs0],
    retract_saved_sympath_lst(Arg, Xs0).
retract_saved_sympath_lst(_Arg, []).

assertz_saved_sympath_lst(Arg, Xs) :-
    ( member(X, Xs),
        assertz_fact(savedpath(Arg, X)),
        fail
    ; true
    ).

% Negate last condition and find an input model.
% If a model is not found, negate the previous condition and try again.
next_input(InConf, InGoal, NewNegMarks) :-
    retractall_fact(conc_stats(_,_,_)),
    retract_saved_sympath(InConf,SymPath,NegMarks),
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
    %
    set_solver_opt(timeout, ~get_nextpath_timeout),
    statistics(walltime, [T0, _]),
    add_constraints(~append(InGoal,~pathgoal(NewSymPath))),
    try_solve(Status),
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
neglastcond_([cond(Constr)|SymPath]) := [~negbool(Constr)|SymPath] :- !.
neglastcond_([_|SymPath]) := ~neglastcond_(SymPath) :- !.

% Remove last condition (fail if no more conditions)
removelastcond(SymPath) := NSymPath :-
    SymPath1 = ~reverse(SymPath),
    SymPath2 = ~removelastcond_(SymPath1),
    NSymPath = ~reverse(SymPath2).

removelastcond_([cond(_)|SymPath]) := SymPath :- !.
removelastcond_([_|SymPath]) := ~removelastcond_(SymPath) :- !.

% ---------------------------------------------------------------------------

:- use_module(library(assoc)).

melt(X,Y) :- empty_assoc(Dic0), melt1(X,Y,Dic0,_).

melt1(X,Y,Dic0,Dic) :- X = '$VAR'(I), !,
    ( get_assoc(I, Dic0, Y0) -> Y = Y0, Dic = Dic0
    ; put_assoc(I, Dic0, Y, Dic)
    ).
melt1(X,X,Dic,Dic) :- atomic(X), !.
melt1(X,Y,Dic0,Dic) :- functor(X,F,N), functor(Y,F,N), meltargs(1,N,X,Y,Dic0,Dic).

meltargs(I,N,_,_,Dic,Dic) :- I > N, !.
meltargs(I,N,X,Y,Dic0,Dic) :-
    arg(I,X,Xi),
    melt1(Xi,Yi,Dic0,Dic1),
    arg(I,Y,Yi),
    I1 is I+1,
    meltargs(I1,N,X,Y,Dic1,Dic).

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


