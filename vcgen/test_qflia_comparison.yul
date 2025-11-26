object "TestLinearComparison" {
    code {
        function test_comparison(x) {
            if gt(x, 100) {
                invalid()
            }
        }
    }
}
