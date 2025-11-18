// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Escrow {
    address public payer;
    address payable public payee;
    address public arbiter;
    uint public amount;
    bool public released;

    constructor(address payable _payee, address _arbiter) payable {
        payer = msg.sender;
        payee = _payee;
        arbiter = _arbiter;
        amount = msg.value;
        released = false;
    }

    function release() public {
        require(msg.sender == arbiter, "Only arbiter");
        require(!released, "Already released");

        released = true;
        payee.transfer(amount);

        assert(released == true);
    }
}
