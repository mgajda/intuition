// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// SafeMath library pattern (built-in in 0.8+, but demonstrates overflow checks)
library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        assert(c >= a); // Overflow check
        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        assert(b <= a); // Underflow check
        return a - b;
    }

    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        assert(c / a == b); // Overflow check
        return c;
    }
}

contract MathTest {
    using SafeMath for uint256;

    function testAdd(uint256 x, uint256 y) public pure returns (uint256) {
        return x.add(y);
    }

    function testMul(uint256 x, uint256 y) public pure returns (uint256) {
        return x.mul(y);
    }
}
