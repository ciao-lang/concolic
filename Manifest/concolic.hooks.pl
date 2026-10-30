:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title, "Bundle Hooks for Concolic").

:- use_module(ciaobld(third_party_install), [auto_install/2]).

% Z3 (third-party component, binary distribution; the z3 executable,
% run as a process, is linked in third-party/bin)
:- def_third_party(z3, [
    version('5.1.0'),
    source_url('DARWINaarch64', zip('https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-arm64-osx-13.3.zip')),
    source_md5('DARWINaarch64', "1d9b15805d98d7c0722d74ae26a3c546"),
    source_url('DARWINx86_64', zip('https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-osx-13.3.zip')),
    source_url('LINUXx86_64', zip('https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-glibc-2.39.zip')),
    source_md5('LINUXx86_64', "d2584a23dee2937fbc4920552dcae958"),
    source_url('LINUXaarch64', zip('https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-arm64-glibc-2.38.zip')),
    build_system(prebuilt),
    libdir(bin)
]).

'$builder_hook'(prepare_build_bin) :-
    auto_install(concolic, z3).
