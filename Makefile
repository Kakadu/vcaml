OUT=./main.exe 

.PHONY: dep test tests celan watch

all:
	@dune build $(OUT)

dep:
	opam install . --deps-only --yes

tests: test
test:
	@dune runtest

watch:
	dune build $(OUT) -w

celan: clean
clean:
	@dune clean
	@$(RM) examples/*.cmi -f

