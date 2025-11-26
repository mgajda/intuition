object "SimpleTest" {
    code {
        function test_comparison(x, y) -> result {
            // Simple comparison - should route to QF_LIA
            if lt(x, 32) {
                result := 1
            }
            if gt(y, 100) {
                result := add(result, 1)
            }
        }

        function test_division(a, b) -> result {
            // Division - should route to QF_BV
            if gt(b, 0) {
                result := div(a, b)
            }
        }

        function test_shift(value) -> result {
            // Shift operation - should route to QF_BV
            result := shl(64, value)
        }

        // Test assertions
        {
            let x := 10
            let y := 200
            let cmp_result := test_comparison(x, y)

            // Assertion: result should be 2
            if iszero(eq(cmp_result, 2)) {
                revert(0, 0)
            }

            let a := 100
            let b := 5
            let div_result := test_division(a, b)

            // Assertion: 100 / 5 = 20
            if iszero(eq(div_result, 20)) {
                revert(0, 0)
            }

            let shift_result := test_shift(1)
            // Assertion: 1 << 64 = 2^64
            if lt(shift_result, 0x10000000000000000) {
                revert(0, 0)
            }
        }
    }
}
