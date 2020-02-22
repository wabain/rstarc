# rstarc

This is a compiler for [Rockstar](https://github.com/dylanbeattie/rockstar), a dynamically typed language whose programs are song lyrics. To my knowledge, it is the only implementation which compiles to machine code instead of interpreting the source or transpiling to an interpreted / jitted language.

The version of the specification it targets is linked in the `spec/` directory. As with any Rockstar implementation, there are some eccentricities and deviations in behavior from the specification. Here are some notable differences:

  * This implementation (as most do) uses IEEE 754 floating-point numbers instead of DEC64 numbers.
  * The specification says that global variables are available after their initialization. In this implementation, variables belong to the outermost scope in which they are referenced, and are `mysterious` until otherwise initialized.
  * Currently, compiled programs cannot perform string concatenation. String concatenation is supported in the interpreter mode.

## Build dependencies

* Python 3.6+

* Poetry 1.0+

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
