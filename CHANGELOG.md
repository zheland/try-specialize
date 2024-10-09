# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2024-10-11
### Added
- `LifetimeFree` trait and implementation for Rust stdlib types.
- `type_eq` functions for `'static` and non-`'static` types.
- `Specialization` struct for comprehensive type specialization.
- `TrySpecialize` trait for simple type specialization
- `TypeFn` trait for specialization types mapping.
- Specialization to `LifetimeFree` type, from `LifetimeFree` type,
  between `'static` types, and `unsafe` variants.
- Specialization by value, by reference, by mutable reference.
- API documentation with examples.
- Tests and doc-tests.
- GitHub CI integration.
- Check and utility scripts.

[Unreleased]: https://github.com/zheland/unwind-context/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/zheland/typed-index-collections/compare/v0.0.0...v0.1.0