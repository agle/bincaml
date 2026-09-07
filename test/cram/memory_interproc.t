  $ cat << EOF | bincaml script -
  > (load-il "../../examples/memory/memory_interproc.il")
  > (run-transforms "ssa")
  > (run-transforms "split-memory-encoding")
  > (run-transforms "memory-specification")
  > (run-transforms "ssa")
  > (run-transforms "linear-const")
  > (run-transforms "linear-copy")
  > (run-transforms "inter-function-summaries")
  > (run-transforms "dynamic-single-assignment")
  > (dump-il "after.il")
  > (dump-boogie "out.bpl")
  > EOF
  (load-il ../../examples/memory/memory_interproc.il)
  (run-transforms ssa)
  (run-transforms split-memory-encoding)
  (run-transforms memory-specification)
  (run-transforms ssa)
  (run-transforms linear-const)
  (run-transforms linear-copy)
  (run-transforms inter-function-summaries)
  (run-transforms dynamic-single-assignment)
  (dump-il after.il)
  (dump-boogie out.bpl)
  $ boogie out.bpl
  
  Boogie program verifier finished with 2 verified, 0 errors

  $ cat << EOF | bincaml script -
  > (load-il "../../examples/memory/memory_interproc.il")
  > (run-transforms "ssa")
  > (run-transforms "flat-memory-encoding")
  > (run-transforms "memory-specification")
  > (run-transforms "ssa")
  > (run-transforms "linear-const")
  > (run-transforms "linear-copy")
  > (run-transforms "inter-function-summaries")
  > (run-transforms "dynamic-single-assignment")
  > (dump-il "after.il")
  > (dump-boogie "out.bpl")
  > EOF
  (load-il ../../examples/memory/memory_interproc.il)
  (run-transforms ssa)
  (run-transforms flat-memory-encoding)
  (run-transforms memory-specification)
  (run-transforms ssa)
  (run-transforms linear-const)
  (run-transforms linear-copy)
  (run-transforms inter-function-summaries)
  (run-transforms dynamic-single-assignment)
  (dump-il after.il)
  (dump-boogie out.bpl)

  $ boogie out.bpl
  out.bpl(302,5): Error: this assertion could not be proved
  Execution trace:
      out.bpl(291,3): b#inputs
  
  Boogie program verifier finished with 1 verified, 1 error
