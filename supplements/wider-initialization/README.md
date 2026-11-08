# Wider initialization supplement

Baseline: FluxWitness-Heat-Conditional-20261108-rc2.zip, SHA-256 d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0.
The three Lean 4.35 declarations extend the allowed initial cosine error to 1e-15 for the same 400-cell, 223-step benchmark. The model's final bound remains 7.05e-9. The conditional driver theorem retains the call, layout and interpretation hypotheses. The reference theorem constructs the finite model trajectory.

The four dump certificates describe local glibc and musl runs. All satisfy even the original RC2 premise. The executable transfer conditions in RC2 still apply.

For a source rebuild, extract a separate copy of RC2. Copy the three supplied lean/*.lean files into its lean/ directory. Append the following lines to that copy's lakefile.lean and run lake build WideDriver WideReference from that directory:

    lean_lib WiderInitial
    lean_lib WideDriver
    lean_lib WideReference

This portable recipe has not been independently tested. The accepted local runs used pinned Lean and cached dependencies. The package records the original object hashes; compiled objects and solver binaries are omitted. Logs may contain paths on the original machine.
