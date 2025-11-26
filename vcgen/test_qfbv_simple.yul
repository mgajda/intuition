object "Test" {
    code {
        function test_linear(x, y) {
            let sum := add(x, y)
            if iszero(gt(sum, x)) {
                revert(0, 0)
            }
        }

        function test_division(a, b) {
            let result := div(a, b)
            if iszero(eq(result, 5)) {
                revert(0, 0)
            }
        }

        function test_shift(value) {
            let shifted := shl(8, value)
            if iszero(gt(shifted, 0)) {
                revert(0, 0)
            }
        }
    }
}
