object "TestDivInline" {
    code {
        function test_div_direct(a, b) {
            if eq(div(a, b), 0) {
                invalid()
            }
        }
    }
}
