# rstarc

This is a compiler for [Rockstar](https://github.com/dylanbeattie/rockstar), a dynamically typed language whose programs are song lyrics. To my knowledge, it is the only implementation which compiles to machine code instead of interpreting the source or transpiling to an interpreted / jitted language.

The version of the specification it targets is linked in the `spec/` directory. As with any Rockstar implementation, there are some excentricities and deviations in behavior. Notably, this implementation (as most do) uses IEEE 754 floating-point numbers.

## Build dependencies

* Python 3.6+

* Pipenv

* Rust 1.30.0+

* LLVM 6

## Building

Build the runtime library, `roll`:

```bash
cd runtime/roll && cargo build --release
```

Build the compiler:

```bash
cargo build [--release]
```

Test:

```bash
./check
```

## Usage

```bash
target/release/rstarc --help
```

## Performance

It's slow! As of now, the language runtime can only allocate memory, so any non-trivial program will tend to accumulate garbage. A garbage collector is in the works (see the `gc` branch), at which point I think doing escape analysis to elide some allocations should make it competitive or superior to transpiling Rockstar implementations.
