// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IERC20 {
    function transfer(address recipient, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
}

contract MaticToUSDC {
    IERC20 public usdcToken;
    address public owner;
    uint256 public conversionRate; // Assume 1 MATIC = conversionRate USDC (scaled by 1e18 for precision)

    event Converted(address indexed user, uint256 maticAmount, uint256 usdcAmount);

    modifier onlyOwner() {
        require(msg.sender == owner, "Only owner can call this function");
        _;
    }

    constructor(address _usdcTokenAddress, uint256 _initialRate) {
        usdcToken = IERC20(_usdcTokenAddress);
        owner = msg.sender;
        conversionRate = _initialRate;
    }

    function setConversionRate(uint256 newRate) external onlyOwner {
        conversionRate = newRate;
    }

    function convert() external payable {
        require(msg.value > 0, "Must send MATIC to convert");

        uint256 usdcAmount = (msg.value * conversionRate) / 1e18;
        require(usdcToken.transfer(msg.sender, usdcAmount), "USDC transfer failed");

        emit Converted(msg.sender, msg.value, usdcAmount);
    }

    function withdrawMatic() external onlyOwner {
        payable(owner).transfer(address(this).balance);
    }

    function withdrawUSDC(uint256 amount) external onlyOwner {
        require(usdcToken.transfer(owner, amount), "USDC transfer failed");
    }
}
