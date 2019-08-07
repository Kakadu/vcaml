all:
	@dune build ./main.exe

test:
	@dune runtest

clean:
	@dune clean

