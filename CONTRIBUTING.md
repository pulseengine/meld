# Contributing to Meld

Welcome! We're glad you're interested in contributing to Meld.

## Development Setup

### Prerequisites

- Rust (stable toolchain)
- Cargo
- Git
- Python (for pre-commit hooks)

### Getting Started

```bash
# Clone the repository
git clone https://github.com/pulseengine/meld.git
cd meld

# Install pre-commit hooks
pip install pre-commit
pre-commit install

# Build the project
cargo build

# Run tests
cargo test
```

## Code Quality

We use several tools to maintain code quality:

### Pre-commit Hooks

We use [pre-commit](https://pre-commit.com/) to run checks before each commit:

- **cargo fmt**: Format code according to Rust style guidelines
- **cargo clippy**: Run static analysis with clippy lints
- **cargo test**: Run all tests

To run pre-commit hooks manually:

```bash
pre-commit run --all-files
```

### Clippy Configuration

Our clippy configuration treats all warnings as errors (`-D warnings`). See [clippy.toml](clippy.toml) for details.

Common clippy lints we enforce:

- `dead_code`: Find unused code
- `unnecessary_lazy_evaluations`: Avoid unnecessary closures
- `unnecessary_cast`: Avoid redundant type casts
- `useless_conversion`: Avoid redundant conversions
- `len_zero`: Prefer `is_empty()` over `len() > 0`
- `clone_on_copy`: Avoid cloning Copy types
- `derivable_impls`: Use `#[derive]` when possible

### Formatting

We use rustfmt for consistent code formatting:

```bash
# Format all code
cargo fmt

# Check formatting
cargo fmt --all -- --check
```

## Testing

Run the full test suite:

```bash
cargo test --all
```

## Pull Request Process

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/your-feature`
3. Make your changes and commit them with pre-commit hooks
4. Push to your fork and submit a pull request
5. Ensure all CI checks pass

## Code Style

- Follow Rust API guidelines
- Use descriptive variable and function names
- Add documentation comments for public APIs
- Keep functions focused and small
- Write tests for new functionality

## Documentation

Update documentation when making changes:

- Update `README.md` for user-facing changes
- Update `CONTRIBUTING.md` for development process changes
- Add doc comments for new public APIs

## License

By contributing to Meld, you agree that your contributions will be licensed under the Apache License 2.0.