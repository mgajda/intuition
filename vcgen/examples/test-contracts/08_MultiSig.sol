// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MultiSig {
    address[] public owners;
    uint public required;
    mapping(address => bool) public isOwner;
    mapping(uint => mapping(address => bool)) public confirmations;
    uint public transactionCount;

    constructor(address[] memory _owners, uint _required) {
        require(_owners.length > 0, "Owners required");
        require(_required > 0 && _required <= _owners.length, "Invalid required");

        for (uint i = 0; i < _owners.length; i++) {
            address owner = _owners[i];
            require(owner != address(0), "Invalid owner");
            require(!isOwner[owner], "Duplicate owner");

            isOwner[owner] = true;
            owners.push(owner);
        }

        required = _required;
    }

    function confirmTransaction(uint transactionId) public {
        require(isOwner[msg.sender], "Not owner");
        require(!confirmations[transactionId][msg.sender], "Already confirmed");

        confirmations[transactionId][msg.sender] = true;
        assert(confirmations[transactionId][msg.sender] == true);
    }
}
