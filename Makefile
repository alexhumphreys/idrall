.PHONY: build

git-submodule-update:
	git submodule update --remote

test-setup:
	echo 3 > /tmp/bar.dhall
	echo './bar.dhall' > /tmp/foo.dhall
	echo './importFailA.dhall' > /tmp/importFailB.dhall
	echo './importFailB.dhall' > /tmp/importFailA.dhall

repl: test-setup
	rlwrap idris2 -p contrib Idrall/API.idr

edit-tests: test-setup
	cd ./tests/idrall/idrall002 && rlwrap idris2 -p contrib -p idrall All.idr

clean:
	rm -f tests/*.idr~
	rm -f tests/*.ibc
	rm -f Idrall/*.idr~
	rm -f Idrall/*.ibc
	rm -rf build/
	rm -rf tests/build/

build:
	idris2 --build idrall.ipkg

install:
	idris2 --install idrall.ipkg

testbin:
	@${MAKE} -C tests testbin

test-only:
	time ${MAKE} -C tests only=$(only)

test: build install testbin test-setup test-only
