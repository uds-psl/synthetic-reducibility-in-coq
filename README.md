# Synthetic Reducibility in Coq

Source code accompanying the [Bachelor's thesis](http://www.ps.uni-saarland.de/~jahn/bachelor/thesis.pdf) of Felix Jahn.
The [project page](http://www.ps.uni-saarland.de/~jahn/bachelor.php) contains
the thesis as well as a [documentation](http://www.ps.uni-saarland.de/~jahn/srt/toc.html) of the
source code.

The main definitions can be found in the file `Definitions_Coq.v`, including the synthetic computability axioms. 

The code was developed in Coq version 8.11.0.

## Compilation
To compile the source code execute:

```
git clone https://github.com/uds-psl/synthetic-reducibility-in-coq.git
cd synthetic-reducibility-in-coq
make
```

## Acknowledgements

The file `Cantor_Pairing_Coq.v` is written by Andrej Dudenhefner.

Parts of the code contained in `Recursive_Mu_Operator_Coq.v` are a adapted version of code proving the witness operator developed in the lecture Introduction to Computational Logic at Saarland University. The original code is available [here](https://www.ps.uni-saarland.de/~smolka/drafts/coq/wo.v).

## License
The code is licensed under the [MIT License](https://github.com/uds-psl/synthetic-reducibility-in-coq/blob/master/LICENSE).
