[![Build Status](https://travis-ci.org/Kakadu/vcaml.svg?branch=master)](https://travis-ci.org/Kakadu/vcaml)

Recommended installation method is using OPAM ((https://launchpad.net/~avsm/+archive/ubuntu/ppa-opam-experimental)[Ubuntu PPA])



### Compile

    dune build main.exe


### Compile & run on input file

    dune exec ./main.exe -- -impl examples/arith.ml
    dune exec ./main.exe -- -impl examples/fib.ml
