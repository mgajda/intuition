object "TestShift" {
    code {
        function test_shift(value) -> result {
            result := shl(8, value)
            if lt(result, value) {
                invalid()
            }
        }
    }
}
