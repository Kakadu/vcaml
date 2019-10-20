.PHONY: dep test tests celan

all:
	@dune build ./main.exe

dep:
	opam install . --deps-only --yes

tests: test
test:
	@dune runtest

celan: clean
clean:
	@dune clean
	@$(RM) examples/*.cmi -f

