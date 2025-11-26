object "TestLinear" {
    code {
        function test_linear(x) {
            if gt(x, 100) {
                invalid()
            }
        }
    }
}
