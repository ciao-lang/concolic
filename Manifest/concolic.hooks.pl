:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title, "Bundle Hooks for Concolic").

:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaobld(builder_aux), [third_party_aux/3]).

'$builder_hook'(prepare_build_bin) :-
	third_party_aux(concolic, z3, ['install_bin_dist']), % Use binary distribution
%	third_party_aux(concolic, z3, ['install_src_dist']), % Use source distribution
%	Conf = ~bundle_path(concolic, 'src/z3_config_auto.pl'),
%	third_party_aux(concolic, z3, ['gen_conf', Conf]).
	true.
