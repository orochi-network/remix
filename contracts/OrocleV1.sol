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


// File contracts/libraries/Bytes.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;

// Index is out of range
error OutOfRange(uint256 requiredLen, uint256 maxLen);

library Bytes {
  // Read address from input bytes buffer
  function readAddress(bytes memory input, uint256 offset) internal pure returns (address result) {
    if (offset + 20 > input.length) {
      revert OutOfRange(offset + 20, input.length);
    }
    assembly {
      result := shr(96, mload(add(add(input, 0x20), offset)))
    }
  }

  // Read unsafe from input bytes buffer
  function readUintUnsafe(bytes memory input, uint256 offset, uint256 bitLen) internal pure returns (uint256 result) {
    assembly {
      result := shr(sub(256, bitLen), mload(add(add(input, 0x20), offset)))
    }
  }

  // Read uint256 from input bytes buffer
  function readUint256(bytes memory input, uint256 offset) internal pure returns (uint256 result) {
    if (offset + 32 > input.length) {
      revert OutOfRange(offset + 32, input.length);
    }
    assembly {
      result := mload(add(add(input, 0x20), offset))
    }
  }

  // Read a sub bytes array from input bytes buffer
  function readBytes(bytes memory input, uint256 offset, uint256 length) internal pure returns (bytes memory) {
    if (offset + length > input.length) {
      revert OutOfRange(offset + length, input.length);
    }
    bytes memory result = new bytes(length);
    assembly {
      // Seek offset to the beginning
      let seek := add(add(input, 0x20), offset)

      // Next is size of data
      let resultOffset := add(result, 0x20)

      for {
        let i := 0
      } lt(i, length) {
        i := add(i, 0x20)
      } {
        mstore(add(resultOffset, i), mload(add(seek, i)))
      }
    }
    return result;
  }
}


// File contracts/orocle-v1/interfaces/IOrocleAggregatorV1.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error ExistedApplication(uint32 appId);
error InvalidApplication(uint32 appId);
error InvalidApplicationName(bytes24 appName);
error InvalidRoundNumber(uint64 round, uint64 requiredRound);
error UndefinedRound(uint64 round);
error InvalidDataLength(uint256 length);
error UnableToPublishData(bytes data);
error DeactivatedUser(address user);

interface IOrocleAggregatorV1 {
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
   * Check if user is deactivated
   * @param user User address
   * @return status
   */
  function isDeactivated(address user) external view returns (bool);

  /**
   * Get round of a given application
   * @param appId Application ID
   * @return round
   */
  function getMetadata(uint32 appId, bytes20 identifier) external view returns (uint64 round, uint64 lastUpdate);

  /**
   * Get data of an application
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getData(uint32 appId, uint64 round, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return data
   */
  function getLatestData(uint32 appId, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return round lastUpdate data
   */
  function getLatestRound(
    uint32 appId,
    bytes20 identifier
  ) external view returns (uint64 round, uint64 lastUpdate, bytes32 data);
}


// File contracts/orocle-v1/Operatable.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error InvalidOperator(address sender);

contract Operatable {
  mapping(address => bool) private operator;

  event AddOperator(address indexed newOperator);
  event RemoveOperator(address indexed OldOperator);

  modifier onlyOperator() {
    if (!operator[msg.sender]) {
      revert InvalidOperator(msg.sender);
    }
    _;
  }

  function _addOperator(address newOperator) internal returns (bool) {
    operator[newOperator] = true;
    emit AddOperator(newOperator);
    return true;
  }

  function _removeOperator(address oldOperator) internal returns (bool) {
    operator[oldOperator] = false;
    emit RemoveOperator(oldOperator);
    return true;
  }

  function _isOperator(address checkAddress) internal view returns (bool) {
    return operator[checkAddress];
  }

  function isOperator(address checkAddress) external view returns (bool) {
    return _isOperator(checkAddress);
  }
}


// File contracts/orocle-v1/OrocleV1.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;




contract OrocleV1 is IOrocleAggregatorV1, Ownable, Operatable {
  using Bytes for bytes;

  // Maping unique fingerprint to data
  mapping(bytes32 => bytes32) private database;

  // Mapping application ID ++ identifier to application metadata
  mapping(bytes32 => bytes32) private metadata;

  // Deactivated user
  mapping(address => bool) private deactivated;

  // Publish new data
  event PublishData(uint32 indexed application, uint64 indexed round, bytes20 indexed identifier, bytes32 data);

  // Request new data
  event Request(address indexed actor, uint256 indexed identifier, bytes indexed data);

  // Fulfill request
  event FulFill(address indexed actor, uint256 indexed identifier, bytes indexed data);

  // Deactivated user status update
  event Deactivated(address indexed actor, bool indexed status);

  // Only active user
  modifier onlyActive() {
    if (deactivated[msg.sender]) {
      revert DeactivatedUser(msg.sender);
    }
    _;
  }

  /**
   * Create new oracle
   */
  constructor(address[] memory operatorList) {
    for (uint256 i = 0; i < operatorList.length; i += 1) {
      _addOperator(operatorList[i]);
    }
  }

  //=======================[  External  ]====================

  /**
   * Emit event when a new request is created
   * @param identifier Data identifier
   * @param data Data
   */
  function request(uint256 identifier, bytes calldata data) external returns (bool) {
    emit Request(msg.sender, identifier, data);
    return true;
  }

  /**
   * Fulfill request
   * @param identifier Data identifier
   * @param data Data
   */
  function fulfill(uint256 identifier, bytes calldata data) external returns (bool) {
    emit FulFill(msg.sender, identifier, data);
    return true;
  }

  //=======================[  Owner  ]====================

  /**
   * Set new operator
   * @param newOperator New operator address
   * @return success
   */
  function addOperator(address newOperator) external onlyOwner returns (bool) {
    return _addOperator(newOperator);
  }

  /**
   * Remove old operator
   * @param oldOperator New operator address
   * @return success
   */
  function removeOperator(address oldOperator) external onlyOwner returns (bool) {
    return _removeOperator(oldOperator);
  }

  //=======================[  Operator  ]====================

  // Set deactivated status
  function setDeactivatedStatus(address userAddress, bool status) external onlyOperator returns (bool) {
    _setDeactivateStatus(userAddress, status);
    return true;
  }

  /**
   * Publish data to database
   * @param packedData packed data
   * @return success
   */
  function publishData(uint32 appId, bytes memory packedData) external onlyOperator returns (bool) {
    // Decode appId and chunksize
    bytes20 identifier;
    bytes32 data;
    if (packedData.length % 52 != 0) {
      revert InvalidDataLength(packedData.length);
    }
    for (uint256 i = 0; i < packedData.length; i += 52) {
      identifier = bytes20(uint160(packedData.readUintUnsafe(i, 160)));
      data = bytes32(uint256(packedData.readUint256(i + 20)));
      if (!_publish(appId, identifier, data)) {
        revert UnableToPublishData(packedData.readBytes(i, 52));
      }
    }
    return true;
  }

  // Dedicated function for price
  function publishPrice(bytes memory packedData) external onlyOperator returns (bool) {
    // Decode appId and chunksize
    bytes20 identifier;
    bytes32 data;
    if (packedData.length % 24 != 0) {
      revert InvalidDataLength(packedData.length);
    }
    for (uint256 i = 0; i < packedData.length; i += 24) {
      identifier = bytes20(bytes8(uint64(packedData.readUintUnsafe(i, 64))));
      data = bytes32(uint256(uint64(packedData.readUintUnsafe(i + 8, 128))));
      if (!_publish(1, identifier, data)) {
        revert UnableToPublishData(packedData.readBytes(i, 24));
      }
    }
    return true;
  }

  //=======================[  Interal  ]====================

  // Set deactivated status
  function _setDeactivateStatus(address userAddress, bool status) internal {
    deactivated[userAddress] = status;
    emit Deactivated(userAddress, status);
  }

  // Publish data to Orocle
  function _publish(uint32 appId, bytes20 identifier, bytes32 data) internal returns (bool) {
    (uint64 round, ) = _getMetadata(appId, identifier);
    round += 1;
    // After 255 round, we will reuse the same slot, it saving a lot of gas
    database[_encodeDataKey(appId, round, identifier)] = data;
    emit PublishData(appId, round, identifier, data);
    _setMetadata(appId, identifier, round);
    return true;
  }

  // Set application round
  function _setMetadata(uint32 appId, bytes20 identifier, uint64 round) internal {
    metadata[_encodeRoundKey(appId, identifier)] = _encodeMetadata(round, uint64(block.timestamp));
  }

  //=======================[  Interal View  ]====================

  // Encode data key
  function _encodeDataKey(uint32 appId, uint64 round, bytes20 identifier) internal pure returns (bytes32 dataKey) {
    assembly {
      dataKey := identifier
      dataKey := or(dataKey, shl(160, and(round, 0xff)))
      dataKey := or(dataKey, shl(224, appId))
    }
  }

  // Encode metadata
  function _encodeMetadata(uint64 round, uint64 lastUpdate) internal pure returns (bytes32 dataKey) {
    assembly {
      dataKey := shl(192, round)
      dataKey := or(dataKey, shl(128, lastUpdate))
    }
  }

  // Encode round key
  function _encodeRoundKey(uint32 appId, bytes20 identifier) internal pure returns (bytes32 roundKey) {
    assembly {
      roundKey := identifier
      roundKey := or(roundKey, shl(224, appId))
    }
  }

  // Decode metadata
  function _decodeMetadata(bytes32 metadataRecord) internal pure returns (uint64 round, uint64 lastUpdate) {
    assembly {
      round := shr(192, metadataRecord)
      lastUpdate := shr(128, metadataRecord)
    }
  }

  // Get application round
  function _getMetadata(uint32 appId, bytes20 identifier) internal view returns (uint64 round, uint64 lastUpdate) {
    return _decodeMetadata(metadata[_encodeRoundKey(appId, identifier)]);
  }

  /**
   * Publish data to database
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @param data Data
   */
  function _readDatabase(uint32 appId, uint64 round, bytes20 identifier) internal view returns (bytes32 data) {
    (uint64 onChainRound, ) = _getMetadata(appId, identifier);
    // Can't get > 255 round in the past
    if (round + 255 < onChainRound || round > onChainRound) {
      revert UndefinedRound(round);
    }
    return database[_encodeDataKey(appId, round, identifier)];
  }

  //=======================[  External View  ]====================

  // Check if user is deactivated
  function isDeactivated(address user) external view returns (bool) {
    return deactivated[user];
  }

  /**
   * Get round of a given application
   * @param appId Application ID
   * @return round
   */
  function getMetadata(uint32 appId, bytes20 identifier) external view returns (uint64 round, uint64 lastUpdate) {
    return _getMetadata(appId, identifier);
  }

  /**
   * Get data of an application
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getData(uint32 appId, uint64 round, bytes20 identifier) external view onlyActive returns (bytes32 data) {
    return _readDatabase(appId, round, identifier);
  }

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return data
   */
  function getLatestData(uint32 appId, bytes20 identifier) external view onlyActive returns (bytes32 data) {
    (uint64 round, ) = _getMetadata(appId, identifier);
    data = _readDatabase(appId, round, identifier);
  }

  /**
   * Get latest round and data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return round lastUpdate data
   */
  function getLatestRound(
    uint32 appId,
    bytes20 identifier
  ) external view onlyActive returns (uint64 round, uint64 lastUpdate, bytes32 data) {
    (round, lastUpdate) = _getMetadata(appId, identifier);
    data = _readDatabase(appId, round, identifier);
  }
}
