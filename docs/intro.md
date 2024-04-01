# A Brief Introduction to OrzIR

OrzIR is a modular and extensible compiler infrastructure designed to facilitate the development of
efficient and customizable compilers for various programming languages and hardware platforms. This
project is currently under development to participate in a Compiler Competition.

This project is inspired by [MLIR](https://mlir.llvm.org),
[pliron](https://github.com/vaivaswatha/pliron) and [abstraps](https://github.com/femtomc/abstraps).

This document provides short overview of OrzIR's design, core components, implementation details,
and key concepts.

## Overview

This project is developed with Rust programming language, and makes use of a number of Rust's
features to realize a modular system. The structure of source code is organized as below:

- `orzir`: The collection of dialects, interfaces and verifiers.
- `orzir-core`: The core components of OrzIR, without concrete dialects. The only exception is the
  built-in `DataFlow`, `ControlFlow` and `RegionInterface` interfaces.
- `orzir-macros`: The macros used in OrzIR.

## Core Components

OrzIR consists of several core components, including dialects, operations, types, blocks, regions,
interfaces and verifiers.

### Context and Arena

The entities in the IR are managed by the `Context`, which contains several arenas. `ArenaPtr<...>`
are used to pass the entities between functions and can be `deref`-ed to get the actual entity.

Context also stores the dialects, indexed by the dialect mnemonic, the value names, and the casters
for dynamic casting between trait objects (i.e. interfaces and verifiers).

### Operations

The operation is the most important component, it represents the computation on values,
definition/declaration of symbols and/or control flow information within blocks. Operations can be
implemented in a heterogeneous way as long as the required traits are implemented. Below is an
implementation of the `arith.iadd` operation:

```rust
/// An integer addition operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "arith.iadd"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", num_results = 1)]
pub struct IAddOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The left-hand side operand.
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The right-hand side operand.
    #[operand(1)]
    rhs: ArenaPtr<Value>,
}
```

Most traits can be derived by the corresponding proc-macros. The results and operands can be
designated in the struct definition. For detailed information, please refer to the documentation of
the crates.

Operations are represented with `OpObj`, which is a wrapper around `Box<dyn Op>`. The `OpObj` can be
downcasted to concrete type with `OpObj::as_a<T>()`. To just check the type, `OpObj::is_a<T>()` can
be used.

### Types

Types represent the kind of entities (not just SSA values) that can be manipulated. For each type
entity (with the same field data), there will be only one instance in the system.

Types are similar to operations, except that it requires a singleton-like storage. All the types are
stored with a `UniqueArena`, which keeps a single instance of each type. Note that the IR type with
the same Rust type but different Rust values are considered different.

This implementation is inspired by pliron.

### Blocks and Regions

Blocks are the basic unit of control flow in the IR. The block can accept incoming block arguments
(an alternative to phi nodes) and contain a list of operations.

Regions are a collection of blocks. They can be nested to represent the hierarchical structure of
the program. The region can be used to represent the module, function, loop, if-else, etc.

There are two kinds of regions, just like in MLIR, `Graph` and `SsaCfg`. The `Graph` region does
not have control flow semantics, while the `SsaCfg` region does.

### Interfaces and Verifiers

Because of the modular design, there needs to be a consistent way to interact with the dialects.
OrzIR provides two kinds of traits to achieve this goal: interfaces and verifiers. Interfaces are
used to access/modify the operations/types, while verifiers are used to represent and verify the
inherent properties that the operations/types should have.

The interfaces and verifiers require casting between trait objects in Rust. There are several
approaches to achieve this. For example, the `intertrait` crate, which is used by pliron (and this
OrzIR project in an early stage before), or maybe some manual crafted vtables, as in the `abstraps`.
However, `intertrait` uses `linkme` and some linker magic, and vtables require some unsafe codes,
which is not very ideal (though maybe faster). In OrzIR, the solution is similar to `intertrait`,
that is, maintaining a map of type IDs and the casting functions, but the difference is that all the
casters are stored in the `Context`, and the interfaces/verifiers needs to be registered to the
`Context` before casting. When `#[derive(Op)]` macro is called with `verifiers` and/or `interfaces`
attributes, the casters will be automatically generated, and registered. If a interface is defined
outside of the crate, it needs to be registered manually with `register_caster!` macros.

After registering, `OpObj::impls` (or `TyObj`) and `OpObj::cast_ref` or `OpObj::cast_mut` can be
used to cast the trait objects.

### Mnemonic, Printing and Parsing

To conveniently validate and test the IR, converting from and to a human-readable format is
necessary. The `Print` and `Parse` traits are used to convert the IR to a human-readable format and
vice versa. The `Print` is simple and intuitive, and `Parse` is implemented in a recursive descent
manner.

Each operation, types in the IR have its mnemonic, and the corresponding parse function will
be registered to the `Context` with the mnemonic. During parsing, the parser will first recognize
the mnemonic, and then call the corresponding parse function to construct the operation/type. Below
is an example.

```text
        `<32>` is parsed by the dialect ty-specific parser
                            |
                            ----
%x = arith.iadd %a, %b : int<32>
^^^^^^^^^^^^^^^ ^^^^^^^^^^^^^^^^
|    ---------- |        ---
|    |          |        |
|    |          |        `--- Also a mnemonic (shortcut for `builtin.int`), 
|    |          |             parsed by `<TyObj as Parse>::parse`
|    |          |
|    |          `--- Parse by the dialect op-specific parser
|    |
|    `--- The mnemonic of the operation
|
`--- Parsed by `<OpObj as Parse>::parse`
```

The parsing and printing can be implemented with proc-macro deriving, but the macro only supports
operations currently, for types and other components in the operatuon, manual implementation is
required.

## Todo

This project is not yet complete, and there are still many features to be implemented. The following
is a list of features that are planned to be implemented:

- [ ] More complete dialects.
- [ ] Verifiers and interfaces for dialects.
- [ ] Target-specific dialects (an alternative to backend).
- [ ] Better parsing and printing support for types and other components.
- [ ] Pass manager and optimization passes.
- [ ] Better documentation and examples.
