object "TestDivision" {
    code {
        function test_div(a, b) -> result {
            result := div(a, b)
            if eq(result, 0) {
                invalid()
            }
        }
    }
}
