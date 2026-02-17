# Meld Core Architecture - What It Actually Does

This document explains Meld's architecture in **clear, practical terms** - focusing on what it does, how it works, and why it's designed this way.

## Quick Overview

Meld takes multiple WebAssembly components and fuses them into a single core module:

```mermaid
flowchart LR
    A[Component A.wasm] --> Meld
    B[Component B.wasm] --> Meld
    Meld --> C[Single Fused Module.wasm]
```

**Why this matters:**
- Eliminates runtime linking overhead
- Enables whole-program optimization
- Preserves original component behavior
- Produces single deployable module

## The 5-Stage Fusion Pipeline

Meld processes components through a clear pipeline:

```mermaid
flowchart LR
    Parse --> Resolve --> Merge --> Adapt --> Encode
```

### Stage 1: Parse - Read WebAssembly Components

**What happens:** Converts WASM binary files into structured data

```mermaid
flowchart LR
    WASM_Binary --> Parser --> Component_AST
```

**Details:**
- Validates WASM binary format
- Extracts types, functions, memories
- Builds import/export mappings
- Preserves custom sections

### Stage 2: Resolve - Build Dependency Graph

**What happens:** Figures out who calls whom and in what order

```mermaid
flowchart LR
    Components --> Resolver --> Dependency_Graph
```

**Details:**
- Matches imports to exports
- Topological sorting (who depends on whom)
- Detects dependency cycles
- Plans memory strategy

### Stage 3: Merge - Combine Components

**What happens:** Fuses multiple components into one module

```mermaid
flowchart LR
    Component_A --> Merger
    Component_B --> Merger
    Merger --> Merged_Module
```

**Critical operation:** Index remapping (updating call targets)

### Stage 4: Adapt - Generate Cross-Component Call Code

**What happens:** Creates trampolines for cross-component calls

```mermaid
flowchart LR
    Cross_Calls --> Adapter_Generator --> Trampoline_Code
```

**When needed:**
- Memory copying (separate memories)
- String transcoding
- Function dispatch

**Optimization:** Direct calls when components share memory

### Stage 5: Encode - Write Final WASM

**What happens:** Serializes fused module to WebAssembly binary

```mermaid
flowchart LR
    Merged_Module --> Encoder --> Final_WASM
```

## Component Model

Meld works with standard WebAssembly components:

```mermaid
classDiagram
    class Component {
        +core_modules: CoreModule[]
        +imports: Import[]
        +exports: Export[]
    }

    class CoreModule {
        +types: FunctionType[]
        +functions: Function[]
        +memories: Memory[]
        +code: FunctionBody[]
    }
```

## Memory Strategies

### Multi-Memory (Default)

Each component keeps its own linear memory. The fused module contains N
memories (one per component). Cross-component calls that pass pointers
use adapters with `cabi_realloc` + `memory.copy`.

```mermaid
flowchart TD
    Component_A --> Memory_A
    Component_B --> Memory_B
    Memory_A --> Fused_Module
    Memory_B --> Fused_Module
```

**Pros:** Correct isolation — `memory.grow` in one component cannot
corrupt another's address space
**Cons:** Cross-component pointer-passing calls require adapter overhead

### Shared Memory (Legacy)

All components share a single linear memory. Cross-component calls are
direct (no adapter overhead), but `memory.grow` in any component corrupts
every other component's pointers.

```mermaid
flowchart TD
    Component_A --> Shared_Memory
    Component_B --> Shared_Memory
    Shared_Memory --> Fused_Module
```

**Pros:** Simpler, direct calls, no adapter overhead
**Cons:** Broken when any component uses `memory.grow`

## Cross-Component Calls

### How Resolution Works

```mermaid
flowchart TD
    A[Component A imports 'add'] --> B[Resolver finds]
    B --> C[Component B exports 'add']
    C --> D[Remap call target]
    D --> E[Updated call site]
```

### Direct vs Adapter Calls

**Direct (shared memory mode):**
```mermaid
flowchart TD
    Caller -->|direct| Target_Function
```

**Adapter (multi-memory mode, pointer args):**
```mermaid
flowchart TD
    Caller -->|ptr,len| Adapter
    Adapter -->|cabi_realloc| Callee_Memory
    Adapter -->|memory.copy| Callee_Memory
    Adapter -->|new_ptr,len| Target_Function
```

## Error Handling

**Strategy:** Fail-fast with clear error messages

```mermaid
flowchart TD
    Operation -->|success| Continue
    Operation -->|error| Fail_Fast
```

**Error types:** Parse, Resolution, Merge, Encode

## Connection to Formal Proofs

Each stage has corresponding formal verification:

```mermaid
flowchart TD
    subgraph Implementation
        Parse --> Resolve --> Merge --> Adapt --> Encode
    end

    subgraph Proofs
        Parse_Proofs --> Resolve_Proofs --> Merge_Proofs --> Adapt_Proofs
    end

    Implementation -->|verified by| Proofs
```

**What's proven:**
- Parse: Input validation correctness
- Resolve: Dependency graph correctness
- Merge: Index remapping safety
- Adapt: Call semantics preservation

## Key Design Principles

1. **Deterministic:** Same inputs → same output
2. **Fail-fast:** Errors detected immediately
3. **Memory safe:** Rust + formal proofs
4. **Semantic preservation:** Fused module behaves like original
5. **Modular:** Clear separation between stages

## Practical Example

Fusing two components where A calls B:

```mermaid
flowchart TD
    subgraph Before
        A[Component A] -->|calls| B[Component B]
    end

    subgraph After
        A -->|direct call| B
    end

    Before --> Meld --> After
```

**Result:** Single module with direct function calls, no runtime overhead.

## When to Use Meld

✅ **Good for:** Components designed to work together
✅ **Good for:** Performance-critical applications
✅ **Good for:** Whole-program optimization
❌ **Not for:** Dynamic component loading
❌ **Not for:** Runtime flexibility needs

## Summary

Meld is a **static component fuser** that:
1. Parses WebAssembly components
2. Resolves dependencies
3. Merges components into one
4. Generates adapters if needed
5. Encodes final WASM module

**Key benefit:** Runtime linking overhead eliminated through build-time fusion.
