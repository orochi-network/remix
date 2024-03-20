// Sources flattened with hardhat v2.19.4 https://hardhat.org

// SPDX-License-Identifier: Apache-2.0 AND MIT

// File @openzeppelin/contracts/utils/Context.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// File @orochi-network/contracts/IOrandConsumerV2.sol@v1.2.3

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error InvalidProvider();

interface IOrandConsumerV2 {
  // Consume the verifiable randomness from Orand provider
  // Return false if you want to stop batching
  function consumeRandomness(uint256 randomness) external returns (bool);
}


// File @orochi-network/contracts/IOrocleAggregatorV1.sol@v1.2.3

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error ExistedApplication(uint32 appId);
error InvalidApplication(uint32 appId);
error InvalidApplicationName(bytes24 appName);
error InvalidRoundNumber(uint64 round, uint64 requiredRound);
error UndefinedRound(uint64 round);
error InvalidDataLength(uint256 length);
error UnableToPublishData(bytes data);

interface IOrocleAggregatorV1 {
  struct ApplicationMetadata {
    bytes16 name;
    uint64 lastUpdate;
    uint64 round;
  }

  /**
   * Emit event when a new request is created
   * @param identifier Data identifier
   * @param data Data
   */
  function request(uint256 identifier, bytes calldata data) external returns (bool);

  /**
   * Fulfill request
   * @param identifier Data identifier
   * @param data Data
   */
  function fulfill(uint256 identifier, bytes calldata data) external returns (bool);

  /**
   * Get round of a given application
   * @param appId Application ID
   * @return round
   */
  function getRound(uint32 appId) external view returns (uint256 round);

  /**
   * Get last update timestamp of a given application
   * @param appId Application ID
   * @return lastUpdate
   */
  function getLastUpdate(uint32 appId) external view returns (uint256 lastUpdate);

  /**
   * Get application metadata
   * @param appId Application ID
   * @return app Application metadata
   */
  function getApplication(uint32 appId) external view returns (ApplicationMetadata memory app);

  /**
   * Get data of an application
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getData(uint32 appId, uint64 round, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get data of an application that lower or equal to target round
   * @param appId Application ID
   * @param targetRound Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getDataLte(uint32 appId, uint64 targetRound, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get data of an application that greater or equal to target round
   * Use this if you wan transaction to be happend after crertain round in the future
   * @param appId Application ID
   * @param targetRound Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getDataGte(uint32 appId, uint64 targetRound, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return data Data
   */
  function getLatestData(uint32 appId, bytes20 identifier) external view returns (bytes32 data);
}


// File contracts/examples/DiceGame.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;



error WrongGuessingValue(uint128 guessing);

// Application should be an implement of IOrandConsumerV2 interface
contract DiceGame is IOrandConsumerV2, Ownable {
  // Set new provider
  event SetProvider(address indexed oldProvider, address indexed newProvider);

  // Set new oracle
  event SetOracle(address indexed oldProvider, address indexed newProvider);

  // Fulfill awaiting result
  event Fulfilled(uint256 indexed gameId, uint256 guessed, uint256 indexed result);

  // New guess from player
  event NewGuess(address indexed player, uint256 indexed gameId, uint128 indexed guessed);

  // Game structure
  struct Game {
    uint128 guessed;
    uint128 result;
  }

  // Provider address
  address private orandProvider;

  // Orochi Network oracle
  address private oracle;

  // Game result storage
  mapping(uint256 => Game) private gameResult;

  // Total game
  uint256 private totalGame;

  // Fulfiled randomness
  uint256 private fulfilled;

  // We batching the radomness in one epoch
  uint256 private maximumBatching;

  // Only allow Orand to submit result
  modifier onlyOrandProvider() {
    if (msg.sender != orandProvider) {
      revert InvalidProvider();
    }
    _;
  }

  // Constructor
  constructor(address provider, address oracleAddress) {
    _setProvider(provider);
    _setOracle(oracleAddress);
  }

  //=======================[  Internal  ]====================

  // Set provider
  function _setOracle(address oracleAddress) internal {
    emit SetOracle(oracle, oracleAddress);
    oracle = oracleAddress;
  }

  // Set provider
  function _getOracle() internal view returns (address) {
    return oracle;
  }

  // Set provider
  function _setProvider(address provider) internal {
    emit SetProvider(orandProvider, provider);
    orandProvider = provider;
  }

  // Set provider
  function _getProvider() internal view returns (address) {
    return orandProvider;
  }

  //=======================[  Owner  ]====================

  // Set provider
  function setProvider(address provider) external onlyOwner returns (bool) {
    _setProvider(provider);
    return true;
  }

  // Set oracle
  function setOracle(address oracleAddress) external onlyOwner returns (bool) {
    _setOracle(oracleAddress);
    return true;
  }

  //=======================[  OrandProviderV2  ]====================

  // Consume the result of Orand V2 with batching feature
  function consumeRandomness(uint256 randomness) external override onlyOrandProvider returns (bool) {
    // We keep batching < maximumBatching
    if (fulfilled < totalGame) {
      Game memory currentGame = gameResult[fulfilled];
      currentGame.result = uint128((randomness % 6) + 1);
      gameResult[fulfilled] = currentGame;
      emit Fulfilled(fulfilled, currentGame.guessed, currentGame.result);
      fulfilled += 1;
      return true;
    }
    // We will let the provider know that all are fulfilled
    return false;
  }

  //=======================[  External  ]====================

  // Player can guessing any number in range of 1-6
  function guessingDiceNumber(uint128 guessing) external returns (bool) {
    // Player only able to guessing between 1-6 since it's dice number
    if (guessing < 1 || guessing > 6) {
      revert WrongGuessingValue(guessing);
    }
    gameResult[totalGame] = Game({ guessed: guessing, result: 0 });

    // Request randomness from Orand
    IOrocleAggregatorV1(oracle).request(0, '0x');

    emit NewGuess(msg.sender, totalGame, guessing);
    totalGame += 1;
    return true;
  }

  //=======================[  External View  ]====================

  // Get provider
  function getProvider() external view returns (address) {
    return _getProvider();
  }

  // Get oracle
  function getOracle() external view returns (address) {
    return _getOracle();
  }

  // Get result from smart contract
  function getResult(uint256 gameId) external view returns (Game memory result) {
    return gameResult[gameId];
  }

  function getStateOfGame() external view returns (uint256 fulfill, uint256 total) {
    return (fulfilled, totalGame);
  }
}
