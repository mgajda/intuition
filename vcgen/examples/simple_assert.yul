// Simple Yul program with assertion
// This demonstrates a basic counter increment with overflow check

object "SimpleCounter" {
    code {
        function increment(x) -> result {
            // Check for overflow (simplified)
            if gt(x, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe) {
                invalid()
            }

            result := add(x, 1)

            // Assert result is greater than x (should hold if no overflow)
            if iszero(gt(result, x)) {
                invalid()
            }
        }

        // Test: increment 42
        let value := 42
        let newValue := increment(value)

        // This assertion should hold
        if iszero(gt(newValue, 42)) {
            invalid()
        }
    }
}
