:- module(_, [], [assertions, fsyntax, datafacts, dcg, hiord]).

:- doc(title, "Concolic search").

:- use_module(library(lists)).
:- use_module(concolic(symbolic)).

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

% ---------------------------------------------------------------------------
% NOTE: numbervars/3 and melt/2 are a workaround for a limit in the
%   number of free variables in dynamic predicates

:- use_module(library(write), [numbervars/3]).

:- data saved_sympath/1.

reset_saved_sympath :-
	retractall_fact(saved_sympath(_)).

retract_saved_sympath(X) :-
	retract_fact(saved_sympath(X0)),
	melt(X0, X).

asserta_saved_sympath(X) :-
	\+ \+ (erase_model(X), numbervars(X,1,_), asserta_fact(saved_sympath(X))).

% Negate last condition and find an input model.
% If a model is not found, negate the previous condition and try again.
next_input(InConf, InGoal, NewNegMarks) :-
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
	Goal = ~append(InGoal,~pathgoal(NewSymPath)),
	%
	( get_model(Goal) ->
	    log('[concolic] new input model found'),
	    NewNegMarks = NewNegMarks0
	; log('[concolic] no model found, negate previous condition...'),
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


