git-submodule-update:
	git submodule update --remote

repl-test:
	idris -p lightyear tests/Test.idr
