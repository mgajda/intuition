object "TestRouting" {
    code {
        function test_linear(x) -> result {
            if lt(x, 100) {
                result := add(x, 10)
            }
            if iszero(eq(result, 110)) {
                revert(0, 0)
            }
        }

        function test_shift(value) -> result {
            result := shl(8, value)
            if iszero(gt(result, 0)) {
                revert(0, 0)
            }
        }

        function test_division(a, b) -> result {
            if gt(b, 0) {
                result := div(a, b)
            }
            if iszero(eq(result, 5)) {
                revert(0, 0)
            }
        }
    }
}
