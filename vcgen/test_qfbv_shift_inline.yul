object "TestShiftInline" {
    code {
        function test_shift_direct(value) {
            if lt(shl(8, value), value) {
                invalid()
            }
        }
    }
}
