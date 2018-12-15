:- bundle(concolic).
version('1.0').
depends([
    core-[version>='1.18']
]).
alias_paths([
    concolic = 'src'
]).
lib('src').
