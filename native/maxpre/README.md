# MaxPre 2.2 MaxSAT preprocessor

MaxPre is a preprocessor for MaxSAT and (since version 2.1) multi-objective MaxSAT,
that supports certified preprocessing for (single-objective) MaxSAT via proof logging (since version 2.2).

## Basic use and flags

Compile MaxPre with `make`.

When running MaxPre as a stand-alone tool, the first argument is the instance file (in [WCNF file format](https://maxsat-evaluations.github.io/2022/rules.html#input)) followed by the mode, which can be `preprocess`, `reconstruct` or `solve`. If mode is not given, default mode `preprocess` is assumed.

An example of using the preprocessor:  
```
./maxpre test.wcnf -techniques=[bu]#[buvsrg] -mapfile=test.map > preprocessed.wcnf
./solver < preprocessed.wcnf > sol0.sol
./maxpre sol0.sol reconstruct -mapfile=test.map > solution.sol
```

Another way to do the same thing:  
```
./maxpre test.wcnf solve -solver=./solver -techniques=[bu]#[buvsrg] > solution.sol  
```

## Certified Preprocessing

To use MaxPre with proof logging, use parameter `-proof=<filename.pbp>`.
The following command preprocesses file `input.wcnf`, prints output instance
to file `output.wcnf` and a [pseudo-Boolean proof for equioptimality](https://gitlab.com/MIAOresearch/software/VeriPB) to file `proof.pbp`.

```
./maxpre input.wcnf -proof=proof.pbp > output.wcnf
```

The proof can then be checked with [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) by the following command,
which reads the original instance from file `input.wcnf`, the instance produced by MaxPre from file `output.wcnf` and the proof from file `proof.pbp`.

```
veripb --wcnf input.wcnf proof.pbp output.wcnf
```

To check the proof with formally verified proof checker [CakePB](https://gitlab.com/MIAOresearch/software/cakepb/), run VeriPB with `--proofOutput` parameter to produce kernel proof.
The following command reads the original MaxSAT instance from file `input.wcnf`, the instance produced by MaxPre from file `output.wcnf` and the kernel proof produced by VeriPB from file `kernel_proof.pbp`.

```
./cake_pb_wcnf input.wcnf kernel_proof.pbp output.wcnf
```

More details about certified preprocessing in the following paper.
[comment]: <p>
[comment]: <details>
[comment]: <summary>

Hannes Ihalainen, Andy Oertel, Yong Kiam Tan, Jeremias Berg, Matti Järvisalo, Magnus O. Myreen, and Jakob Nordström.
Certified MaxSAT preprocessing.
IJCAR, 2024.

[comment]: </summary>

```
@inproceedings{IOTBJMN24CertifiedPreprocessing,
  author    = {Hannes Ihalainen and Andy Oertel and Yong Kiam Tan and Jeremias Berg and Matti J{\"{a}}rvisalo and Magnus O. Myreen and Jakob Nordstr{\"{o}}m},
  title     = {Certified MaxSAT preprocessing},
  pages     = {??\nobreakdash--??},
  booktitle = {Proceedings of the 12th International Joint Conference
on Automated Reasoning ({IJCAR}~'24)},
  series    = {??},
  volume    = {??},
  publisher = {??},
  year      = {2024},
}
```
[comment]: </details>
[comment]: </p>

## MaxPre for Multi-Objective Optimization

To use MaxPre (as a stand-alone tool) to preprocess multiobjective optimization problems, use flag `-problemtype=mcnf`.
The input file should be given in MCNF file format, detailed [here](https://bitbucket.org/coreo-group/mo-prepro/src/master/cp23/).

More details on preprocessing for multi-objective instances in the following paper.

[comment]: <p>
[comment]: <details>
[comment]: <summary>

Christoph Jabs, Jeremias Berg, Hannes Ihalainen, and, Matti Järvisalo.
Preprocessing in SAT-Based Multi-Objective Combinatorial Optimization.
CP, 2023.

[comment]: </summary>

```
@inproceedings{JBIJ23PreprocessingMO,
	author    = {Christoph Jabs and Jeremias Berg and Hannes Ihalainen and Matti J{\"{a}}rvisalo},
  title     = {Preprocessing in SAT-Based Multi-Objective Combinatorial Optimization},
  pages     = {18:1\nobreakdash--18:20},
  booktitle = {Proceedings of the 29th International Conference on Principles and Practice of Constraint Programming, ({CP}~'23)},
  series    = {LIPIcs},
  volume    = {280},
  publisher = {Schloss Dagstuhl - Leibniz-Zentrum f{\"{u}}r Informatik},
  year      = {2023},
}
```

[comment]: </details>
[comment]: </p>





## How to Cite MaxPre 2

To cite MaxPre 2, cite one or both of the following papers

[comment]: <p>
[comment]: <details>
[comment]: <summary>

Hannes Ihalainen, Jeremias Berg and Matti Järvisalo.
Clause Redundancy and Preprocessing in Maximum Satisfiability.
CP, 2023.

[comment]: </summary>

```
@inproceedings{IBJ22ClauseRedundancy,
  author    = {Hannes Ihalainen and Jeremias Berg and Matti J{\"{a}}rvisalo},
  title     = {Clause Redundancy and Preprocessing in Maximum Satisfiability},
  pages     = {75\nobreakdash--94},
  booktitle = {Proceedings of the 11th International Joint Conference
               on Automated Reasoning ({IJCAR}~'22)},
  year      = {2022},
  month     = aug,
  series    = {Lecture Notes in Computer Science},
  volume    = {13385},
  publisher = {Springer},
}
```

[comment]: </details>
[comment]: </p>

[comment]: <p>
[comment]: <details>
[comment]: <summary>

Tuukka Korhonen, Jeremias Berg, Paul Saikko and Matti Järvisalo
MaxPre: An Extended MaxSAT Preprocessor.
SAT 2017.

[comment]: </summary>

```
@inproceedings{KBSJMaxPre,
  author    = {Tuukka Korhonen and Jeremias Berg and Paul Saikko and Matti J{\"{a}}rvisalo},
  title     = {Clause Redundancy and Preprocessing in Maximum Satisfiability},
  pages     = {449\nobreakdash--456},
  booktitle = {Proceedings of the 20th International Conference on Theory and Applications of Satisfiability Testing, ({SAT}~'17)},
  year      = {2017},
  series    = {Lecture Notes in Computer Science},
  volume    = {10491},
  publisher = {Springer},
	editor    = {Serge Gaspers and Toby Walsh},
}
```

[comment]: </details>
[comment]: </p>

If you use MaxPre for preprocessing for multi-objective instances, please cite

[comment]: <p>
[comment]: <details>
[comment]: <summary>

Christoph Jabs, Jeremias Berg, Hannes Ihalainen, and, Matti Järvisalo.
Preprocessing in SAT-Based Multi-Objective Combinatorial Optimization.
CP, 2023.

[comment]: </summary>

```
@inproceedings{JBIJ23PreprocessingMO,
	author    = {Christoph Jabs and Jeremias Berg and Hannes Ihalainen and Matti J{\"{a}}rvisalo},
  title     = {Preprocessing in SAT-Based Multi-Objective Combinatorial Optimization},
  pages     = {18:1\nobreakdash--18:20},
  booktitle = {Proceedings of the 29th International Conference on Principles and Practice of Constraint Programming, ({CP}~'23)},
  series    = {LIPIcs},
  volume    = {280},
  publisher = {Schloss Dagstuhl - Leibniz-Zentrum f{\"{u}}r Informatik},
  year      = {2023},
}
```

[comment]: </details>
[comment]: </p>

If you use MaxPre for certified preprocessing, please cite

[comment]: <p>
[comment]: <details>
[comment]: <summary>

Hannes Ihalainen, Andy Oertel, Yong Kiam Tan, Jeremias Berg, Matti Järvisalo, Magnus O. Myreen, and Jakob Nordström.
Certified MaxSAT preprocessing.
IJCAR, 2024.

[comment]: </summary>

```
@inproceedings{IOTBJMN24CertifiedPreprocessing,
  author    = {Hannes Ihalainen and Andy Oertel and Yong Kiam Tan and Jeremias Berg and Matti J{\"{a}}rvisalo and Magnus O. Myreen and Jakob Nordstr{\"{o}}m},
  title     = {Certified MaxSAT preprocessing},
  pages     = {??\nobreakdash--??},
  booktitle = {Proceedings of the 12th International Joint Conference
on Automated Reasoning ({IJCAR}~'24)},
  series    = {??},
  volume    = {??},
  publisher = {??},
  year      = {2024},
}
```

[comment]: </details>
[comment]: </p>


## More detailed information

### Dependencies

MaxPre supports reading input instance in compressed `.xz` and `.gz` formats.
This support uses Boost library.
To compile without Boost and support for compressed formats, compile with option `make with_zlib=0`.

### Preprocess mode

In preprocess mode, MaxPre preprocesses given input file and prints output file in standard output.
Use parameter `-mapfile` to save recostruction map to file (see reconstruct).

### Reconstruct mode

In reconstruct mode, MaxPre reads a solution of a MaxSAT solver (assumed to be in the [standard format](https://maxsat-evaluations.github.io/2022/rules.html#output)) and a reconstruction map from given file.
MaxPre then outputs a reconstructed solution (in the [standard format](https://maxsat-evaluations.github.io/2022/rules.html#output))

The reconstruction also works for multiobjective MaxSAT.
However, there is no currently implementation for support any separate solution format for multiobjective optimization in MaxPre, so the output MaxPre produces will be MaxSAT output format.

### Solve mode

In solve mode, MaxPre preprocesses instance, then invokes a solver defined by parameters `-solver` and `-solverflags`.
The standard output of the solver is directed to a file defined by parameter `-solfile`.
If parameter `-solfile` is not given, default file `sol0.sol` will be used.
Then MaxPre reads the solution from the file and reconstructs and outputs a solution to the original instance.

### API

MaxPre offers an API for integration with MaxSAT solvers. Use `make lib` to make
the static library file and include `preprocessorinterface.hpp` to use it. The API
is documented in `preprocessorinterface.hpp` and supports single and
multi-objective problems.

### Preprocessing Techniques

`-techniques` (string, default: `[bu]#[buvsrgc]`)

This string defines the preprocessing techniques to use and the order of them.  
Each letter corresponds to a preprocessing technique. Each preprocessing technique is applied until its fixpoint.  
Techniques inside brackets are applied until all of them are in fixpoint. The brackets work recursively.  
If a `#` character is given, all techniques before it are applied before group detection and adding labels (techniques available before labeling are BCE, UP and SE).  

| character | description                      |
| --------- | -------------------------------- |
| `b`       | blocked clause elimination       |
|	`u`       | unit propagation                 |
| `v`       | bounded variable elimination     |
| `s`       | subsumption elimination          |
| `r`       | self subsuming resolution        |
| `l`       | subsumed label elimination       |
| `c`       | binary core removal              |
| `a`       | bounded variable addition        |
| `g`       | group subsumed label elimination |
| `e`       | equivalence elimination          |
| `h`       | unhiding techniques (on binary implication graph, failed literals, hidden tautology elimination, hidden literal elimination) |
| `t`       | structure labeling               |
| `G`       | intrinsic atmost1 constraints    |
| `T`       | TrimMaxSAT                       |
| `V`       | TrimMaxSAT-algorithm on all variables to detect backbones |
| `H`       | hardening                        |
| `R`       | failed literal elimination       |

### Other Flags

`-solver` (string, default: disabled)

The solver to use to solve the preprocessed instance

`-solverflags` (string, default: disabled)

The flags to use with the solver
For example `-solver=./LMHS -solverflags="--infile-assumps --no-preprocess"` results in using the command `./LMHS preprocessed.wcnf --infile-assumps --no-preprocess > sol0.sol`

`-mapfile` (string, default: disabled)

The file to write the solution reconstruction map

`-problemtype` (string: `{maxsat, sat, mcnf}`, default: `maxsat`)

Should the problem be preprocessed as a MaxSAT, multi-objective MaxSAT, or SAT instance

`-outputformat` (string: `{auto, wpms, wpms22, sat, mcnf}`, default: `wpms22`)
Defines the format in which the preprocessed instance is printed.
When option `auto` is selected, the outputformat will be same as the format of the input file.

`-solutionformat` (string: `{auto, wpms, wpms22}`, default: `wpms22`/`auto`)
Defines the format in which the solution is printed when `solve` or `reconstruct` mode is used.
The option `auto` is available only in `solve` mode (where it is the default value), and when it is selected, the format will be same as the outputformat.

`-solversolutionformat` (string: `{auto, wpms, wpms22}`, default: `wpms22`/`auto`)
Defines the format of the solver output when `solve` or `reconstruct` mode is used.
The option `auto` is available only in `solve` mode (where it is the default value), and when it is selected, the format will be same as the outputformat.

`-timelimit` (double: `[0, 500000000]`, default: `inf`)

Limit for preprocessing time in seconds

`-skiptechnique` (int: `[1, 1000000000]`, default: disabled)

Skip a preprocessing technique if it seems to be not effective in x tries (x is given in this flag)
Recommended values for this could be something between 10 and 1000

`-matchlabels` (bool: `{0, 1}`, default: 0)

Use label matching technique to reduce the number of labels

`-bvegate` (bool: `{0, 1}`, default: 0)

Use BVE gate extraction to extend BVE
Note: applying BCE will destroy all recognizable gate structures

`-verb` (int: `[0, 1]`, default: 1)

If verb is 0 the preprocessor will output less stuff to the standard error


### Actual order of simplifications

* remove tautologies
* remove empty clauses
* remove duplicate clauses
* apply preprocessing techniques specified before the #-character
* remove empty clauses
* group detection
* label creation
* label matching (if enabled)
* remove duplicate clauses
* apply preprocessing techniques
* remove empty clauses
* remove duplicate clauses

### The techniques string

Each technique is applied somewhat modularly indenpendent of each other. The user
can specify the exact order of used preprocessing techniques with the techniques string.
Per default, each technique is always applied until "fixpoint" - the point after which that
technique is unable to simplify the instance further. The exception to this is
The techniques inside brackets are applied
until none of them change the instance when applying all of them in the given order.
The brackets work recursively, for example `[[[[vu]b]sr]ea]` is valid syntax.

### Timelimit

You can set internal time limit for the preprocessor running time with the timelimit flag.
The preprocessor will try to preprocess the instance in less than the given time,
however it is hard to estimate I/O times with large files, so when preprocessing very
large instances you should take that into account. The preprocessor tries to limit
the time used by each of the preprocessing techniques somewhat independly of each other.
Each technique will be allocated its own time limit (the proportions of time given
to each preprocessing technique are hardcoded in log.cpp file in Log::timePlan
function. When some techniques do not use all of their allocated time, it will be
given to other techniques with some heuristics. Note that by specifying the timelimit,
the preprocessor might work less efficiently overall. For example it could preprocess
everything to fixpoint in 60 seconds without the timelimit flag, but with -timelimit=60
it could use only 30 seconds not get as much preprocessing done. It is not recommended
to try to optimize the time used by the preprocessor by using the timelimit flag, but
rather to use it for an upper bound for the time used by the preprocessor.
