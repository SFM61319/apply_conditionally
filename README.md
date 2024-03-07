# Apply Conditionally

_Chain and apply methods on objects conditionally._

## Installation

1. Using `cargo`:

```sh
cargo add apply_conditionally
```

2. By updating `Cargo.toml`:

```toml
[dependencies]
apply_conditionally = "1.0.0"
```

## Usage

```rs
// Bring the trait into scope to access the trait methods on objects
use apply_conditionally::ApplyConditionally;

fn foo<T>(value: T, condition: bool) {
    value
        .apply(bar)
        .apply_if(condition, baz)
        .some_other_method();
}
```

## License

[Licensed](LICENSE "Click to open the license file") under the [MIT License](https://opensource.org/license/MIT "Click to view the license text").
