// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Voting {
    struct Proposal {
        string name;
        uint voteCount;
    }

    address public chairperson;
    mapping(address => bool) public voters;
    mapping(address => uint) public votes;
    Proposal[] public proposals;

    constructor(string[] memory proposalNames) {
        chairperson = msg.sender;
        for (uint i = 0; i < proposalNames.length; i++) {
            proposals.push(Proposal({
                name: proposalNames[i],
                voteCount: 0
            }));
        }
    }

    function giveRightToVote(address voter) public {
        require(msg.sender == chairperson, "Only chairperson");
        require(!voters[voter], "Already voted");
        voters[voter] = true;
    }

    function vote(uint proposal) public {
        require(voters[msg.sender], "No right to vote");
        require(votes[msg.sender] == 0, "Already voted");

        votes[msg.sender] = proposal + 1;
        proposals[proposal].voteCount += 1;

        assert(votes[msg.sender] > 0);
    }
}
