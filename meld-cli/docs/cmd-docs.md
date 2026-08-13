# meld docs [topic]

This documentation, embedded in the binary (offline, air-gapped by
construction). `meld docs` lists topics; `meld docs <topic>` shows one;
`--grep <q>` searches across all topic bodies and titles; `--format json`
emits the list (or a single topic, with its body) as JSON for machine queries,
modelled on `rivet docs`.

`meld docs check --coverage` asserts that every top-level CLI subcommand has a
documented topic whose slug matches the subcommand name; `--strict` exits
non-zero on any gap, so an undocumented subcommand cannot ship (a CI gate, not
review discipline). This is the mechanical invariant behind safety requirement
SR-64.
