# Meld STPA Control Structure Diagram

## High-Level Control Structure

```mermaid
flowchart TD
    subgraph "External Environment"
        BUILD["Build System / Developer<br/>(CTRL-BUILD)"]
    end

    subgraph "Meld System Boundary"
        CLI["Meld CLI<br/>(CTRL-CLI)"]
        PARSER["Parser<br/>(CTRL-PARSER)"]
        RESOLVER["Resolver<br/>(CTRL-RESOLVER)"]
        MERGER["Merger<br/>(CTRL-MERGER)"]
        ADAPTER["Adapter Generator<br/>(CTRL-ADAPTER)"]

        subgraph "Controlled Processes"
            COMP["Component Binary Data"]
            DEP["Dependency Graph"]
            IDX["Merged Index Space"]
            TRAMP["Adapter Trampoline Code"]
            OUT["Output Encoding"]
        end
    end

    BUILD -->|"config, components"| CLI
    CLI -.->|"exit code, errors, stats"| BUILD

    CLI -->|"component bytes"| PARSER
    PARSER -.->|"parsed structures, errors"| CLI

    CLI -->|"parsed components"| RESOLVER
    RESOLVER -.->|"resolved graph, CopyLayouts"| CLI

    CLI -->|"resolved graph"| MERGER
    MERGER -.->|"merged module, index maps"| CLI

    CLI -->|"merge result, CopyLayouts"| ADAPTER
    ADAPTER -.->|"adapter functions"| CLI

    CLI -->|"final module"| OUT

    PARSER -->|"validate, extract"| COMP
    COMP -.->|"sections, types"| PARSER

    RESOLVER -->|"match, sort"| DEP
    DEP -.->|"pairs, order"| RESOLVER

    MERGER -->|"rebase, rewrite"| IDX
    IDX -.->|"index maps"| MERGER

    ADAPTER -->|"generate trampolines"| TRAMP
    TRAMP -.->|"wasm instructions"| ADAPTER
```

## Adapter Generator Detail (CTRL-ADAPTER)

```mermaid
flowchart TD
    ADAPT["Adapter Generator"]

    ADAPT -->|"CA-ADAPT-1: generate adapter"| TRAMP["Trampoline Code"]
    ADAPT -->|"CA-ADAPT-2: cabi_realloc"| CALLEEALLOC["Callee Memory Allocation"]
    ADAPT -->|"CA-ADAPT-3: memory.copy"| DATACOPY["Cross-Memory Data Copy"]
    ADAPT -->|"CA-ADAPT-4: fixup loop"| PTRFIX["Inner Pointer Fixup"]
    ADAPT -->|"CA-ADAPT-5: transcode"| STRCONV["String Transcoding"]

    TRAMP -.->|"function index"| ADAPT
    CALLEEALLOC -.->|"dest pointer"| ADAPT
    DATACOPY -.->|"bytes copied"| ADAPT
    PTRFIX -.->|"pointers fixed"| ADAPT
    STRCONV -.->|"transcoded bytes"| ADAPT
```

## Legend

- **Solid arrows** (-->) = Control actions (commands flowing downward)
- **Dashed arrows** (-..->) = Feedback (information flowing upward)
- Each controller has a process model (internal beliefs) used to make decisions
- STPA does not assume obedience: control actions may not be executed correctly
