.PHONY: test tests celan

all:
	@dune build ./main.exe

tests: test
test:
	@dune runtest

celan: clean
clean:
	@dune clean

