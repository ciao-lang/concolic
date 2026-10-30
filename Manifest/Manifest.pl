:- bundle(concolic).
version('1.0').
depends([
    core-[version>='1.26']
]).
alias_paths([
    concolic = 'src'
]).
lib('src').
