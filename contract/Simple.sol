// SimpleToken.sol
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract SimpleToken is ERC20 {
    constructor() ERC20("Simple Token", "ST") {
        _mint(msg.sender, 1000000000 * 10 ** uint(decimals()));
    }
}
