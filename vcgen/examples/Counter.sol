// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * Simple Counter contract for demonstrating hevm symbolic execution
 *
 * This contract has:
 * - An increment function with overflow protection
 * - An assertion that should always hold
 */
contract Counter {
    uint256 public count;

    /// Increment counter with overflow check
    function increment() public {
        require(count < type(uint256).max, "Overflow protection");
        count = count + 1;

        // This assertion should always hold after increment
        assert(count > 0);
    }

    /// Set counter to specific value
    function set(uint256 newCount) public {
        count = newCount;
    }

    /// Increment by a specific amount
    function incrementBy(uint256 delta) public {
        require(count + delta >= count, "Overflow");
        count = count + delta;

        // Assertion: count increased by at least delta
        assert(count >= delta);
    }

    /// Decrement counter
    function decrement() public {
        require(count > 0, "Underflow protection");
        count = count - 1;
    }
}
