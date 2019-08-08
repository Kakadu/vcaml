.PHONY: test tests

all:
	@dune build ./main.exe

tests: test
test:
	@dune runtest

clean:
	@dune clean

