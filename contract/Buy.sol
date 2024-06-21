// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IERC20 {
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
}

contract BuyUSDC {
    address public usdcTokenAddress;

    event USDCBought(address indexed buyer, uint256 amount);

    constructor(address _usdcTokenAddress) {
        usdcTokenAddress = _usdcTokenAddress;
    }

    function buyUSDC(uint256 amount) public {
        require(amount > 0, "Amount should be greater than zero");
        IERC20(usdcTokenAddress).transferFrom(msg.sender, address(this), amount);
        emit USDCBought(msg.sender, amount);
    }
}
