// Simple test for WP calculus
object "WPTest" {
    code {
        // Simple increment with postcondition
        let x := 42
        let result := add(x, 1)

        // Assert: result > x (should verify with WP!)
        if iszero(gt(result, x)) {
            invalid()
        }
    }
}
