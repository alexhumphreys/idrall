.PHONY: build

export IDRALL_TEST=True

git-submodule-update:
	git submodule update --remote

test-setup:
	echo 3 > /tmp/bar.dhall
	echo './bar.dhall' > /tmp/foo.dhall
	echo './importFailA.dhall' > /tmp/importFailB.dhall
	echo './importFailB.dhall' > /tmp/importFailA.dhall

demo: test-setup
	rlwrap -n idris2 -p contrib  Idrall/Demo.idr

repl: test-setup
	rlwrap -n idris2 -p contrib Idrall/APIv1.idr

repl2: test-setup
	rlwrap idris2 -p contrib Idrall/Derive/ToDhall.idr --log 0
edit-tests: test-setup
	cd ./tests/idrall/idrall002 && rlwrap -n idris2 -p contrib -p test -p idrall All.idr

edit-tests-one: test-setup
	cd ./tests/idrall/idrall004 && rlwrap -n idris2 -p contrib -p test -p idrall One.idr

edit-tests-derive: test-setup
	cd ./tests/derive/derive002 && rlwrap -n idris2 -p contrib -p test -p idrall Main.idr

clean:
	rm -f tests/*.idr~
	rm -f tests/*.ibc
	rm -f Idrall/*.idr~
	rm -f Idrall/*.ibc
	rm -rf build/
	rm -rf tests/build/
	rm -rf tests/*/*/build
	@${MAKE} -C tests clean

build:
	idris2 --build idrall.ipkg

install:
	idris2 --install idrall.ipkg

testbin:
	@${MAKE} -C tests testbin

test-only:
	${MAKE} -C tests only=$(only)

test: build install testbin test-setup test-only

time:
	time ${MAKE} test INTERACTIVE=''
