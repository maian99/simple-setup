{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}

module Main where

import Control.Lens
import Control.Monad (void)
import Data.Aeson (FromJSON, ToJSON)
import Data.Either.Combinators (rightToMaybe)
import Data.Monoid (Last (Last))
import GHC.Generics
import Wallet.Emulator (knownWallet)
import qualified Data.Map as M
import qualified Ledger
import qualified Ledger.Ada as Ada
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Scripts as Scripts
import qualified Ledger.Typed.Scripts as TScripts
import qualified Ledger.Value as Value
import qualified Plutus.Contract as Contract
import qualified Plutus.Contracts.Currency as Currency
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import qualified PlutusTx.Prelude as PL
import qualified PlutusTx.Trace as PTrace

import Prelude

data CDPDatum 
  = ManagerDatum 
    { getUsers  :: [Ledger.PubKeyHash] } 
  | UserDatum 
    { getPubKey :: Ledger.PubKeyHash
    , getLocked :: Integer
    , getMinted :: Integer }

data EPT
  = EPT 
    { getAToken :: Value.AssetClass
    , getUToken :: Value.AssetClass
    , getAmount :: Integer } 
  deriving (FromJSON, ToJSON, Generic)

data CDPParams
  = CDPParams 
    { ogetAToken :: Value.AssetClass  
    , ogetUToken :: Value.AssetClass }

data CDP

data CDPActions 
  = MkOpen Ledger.PubKeyHash 
  | MkToken Integer
  | MkBalance Integer

PlutusTx.unstableMakeIsData ''CDPActions
PlutusTx.unstableMakeIsData ''CDPDatum
PlutusTx.unstableMakeIsData ''CDPParams
PlutusTx.unstableMakeIsData ''EPT
PlutusTx.makeLift ''CDPParams

instance TScripts.ValidatorTypes CDP where
  type DatumType CDP = CDPDatum
  type RedeemerType CDP = CDPActions

{-# INLINEABLE mkValidator #-}
mkValidator :: CDPParams -> CDPDatum -> CDPActions -> Ledger.ScriptContext -> Bool
mkValidator CDPParams{..} d act ctx = 
  case act of 
    MkOpen k ->
      case d of
        ManagerDatum l ->
          PTrace.traceIfFalse "Inputs do not contain the real Manager" (inVal == nftVal) &&
          PTrace.traceIfFalse "Wrong signature" (Ledger.txSignedBy info k) &&
          PTrace.traceIfFalse "Invalid manager datum" (managerDatumList l k) &&
          PTrace.traceIfFalse "Invalid user datum" (checkUserDatum k 0 0)  &&
          PTrace.traceIfFalse "Invalid user output value" (checkUserValue atkVal) &&
          PTrace.traceIfFalse "Invalid manager output value" (checkManagerValue nftVal)
        _ -> PTrace.traceError "Invalid datum" False
    MkBalance a ->
      case d of
        UserDatum k lk mt ->
          PTrace.traceIfFalse "Invalid changes to the locked ADA" (a PL./= 0 && (lk PL.+ a) PL.>= 0) &&
          PTrace.traceIfFalse "Wrong signature" (Ledger.txSignedBy info k) &&
          PTrace.traceIfFalse "Invalid input" (inVal == atkVal <> Ada.lovelaceValueOf lk) &&
          PTrace.traceIfFalse "Invalid user output value" (checkUserValue (atkVal <> Ada.lovelaceValueOf lk <> Ada.lovelaceValueOf a)) &&
          PTrace.traceIfFalse "Invalid user output datum" (checkUserDatum k (lk PL.+ a) mt) &&
          PTrace.traceIfFalse "Invalid collateral ratio" (a PL.< 0 && maintainRatio (lk PL.+ a) mt)
        _ -> PTrace.traceError "Invalid datum" False
    MkToken a ->
      case d of
        UserDatum k lk mt ->
          PTrace.traceIfFalse "Invalid changes to the Token amount" (a PL./= 0 && mt PL.+ a PL.>= 0) && 
          PTrace.traceIfFalse "Wrong signature" (Ledger.txSignedBy info k) &&
          PTrace.traceIfFalse "Invalid input" (inVal == atkVal <> Ada.lovelaceValueOf lk) &&
          PTrace.traceIfFalse "Invalid user output value" (checkUserValue (atkVal <> Ada.lovelaceValueOf lk)) &&
          PTrace.traceIfFalse "Invalid user output datum" (checkUserDatum k lk (mt PL.- a)) &&
          PTrace.traceIfFalse "Invalid collateral ratio" (a PL.< 0 && maintainRatio lk (mt PL.+ a)) &&
          PTrace.traceIfFalse "Wrong token amount" (checkTokenAmount a)
        _ -> PTrace.traceError "Invalid datum" False
  where 
  
    adaPrice :: Integer
    adaPrice = 12

    iTSLAPrice :: Integer
    iTSLAPrice = 7096

    collateralRatio :: Integer
    collateralRatio = 15

    maintainRatio :: Integer -> Integer -> Bool
    maintainRatio lk mt = adaPrice PL.* lk PL.>= collateralRatio PL.* iTSLAPrice PL.* (100000 :: Integer) PL.* mt
    
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
    
    input :: Ledger.TxInInfo
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> PTrace.traceError "expected exactly one script input"
    
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    checkUserValue :: Value.Value -> Bool
    checkUserValue v = v == (Ledger.txOutValue outUserOutput)
    
    checkManagerValue :: Value.Value -> Bool
    checkManagerValue v = v == (Ledger.txOutValue outManagerOutput)
    
    nftVal :: Value.Value
    nftVal = (Value.assetClassValue ogetAToken 1)
    
    atkVal :: Value.Value
    atkVal = (Value.assetClassValue ogetUToken 1)
      
    ownOutput :: [Ledger.TxOut]
    ownOutput = Ledger.getContinuingOutputs ctx
    
    outManagerOutput :: Ledger.TxOut
    outManagerOutput = case PL.filter isManager ownOutput of
      [o] -> o
      _   -> PTrace.traceError "Expected exactly one Manager output"
    
    outUserOutput :: Ledger.TxOut
    outUserOutput = case PL.filter isUser ownOutput of
      [o] -> o
      _   -> PTrace.traceError "Expected exactly one User output"
      
    outManagerDatum :: CDPDatum
    outManagerDatum = case cdpDatum outManagerOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> PTrace.traceError "Impossible case"
    
    outUserDatum :: CDPDatum
    outUserDatum = case cdpDatum outUserOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> PTrace.traceError "Impossible case"
    
    managerDatumList :: [Ledger.PubKeyHash] -> Ledger.PubKeyHash -> Bool
    managerDatumList l k = case outManagerDatum of
      ManagerDatum (a:as) -> a PL.== k && l PL.== as
      _ -> PTrace.traceError "Invalid manager output datum"
    
    checkUserDatum :: Ledger.PubKeyHash -> Integer -> Integer -> Bool
    checkUserDatum k lk mt = case outUserDatum of
      UserDatum k' lk' mt' -> k PL.== k' && lk' PL.== lk && mt' PL.== mt
      _ -> PTrace.traceError "Wrong user input datum"
    
    isManager :: Ledger.TxOut -> Bool
    isManager os = case cdpDatum os (`Ledger.findDatum` info) of
      Just (ManagerDatum _) -> True
      _ -> False

    isUser :: Ledger.TxOut -> Bool
    isUser os = case cdpDatum os (`Ledger.findDatum` info) of
      Just (UserDatum _ _ _) -> True
      _ -> False

    cdpDatum :: Ledger.TxOut  -> (Scripts.DatumHash -> Maybe Scripts.Datum) -> Maybe CDPDatum
    cdpDatum o f = do
      dh <- Ledger.txOutDatum o
      Scripts.Datum dd <- f dh
      PlutusTx.fromBuiltinData dd

    checkTokenAmount :: Integer -> Bool
    checkTokenAmount amt = case Value.flattenValue (Ledger.txInfoMint info) of
      [(_, _, amt')] -> amt' PL.== amt
      _              -> False    

compiledValidator :: CDPParams -> TScripts.TypedValidator CDP
compiledValidator nft = 
  TScripts.mkTypedValidator @CDP
    ($$(PlutusTx.compile [||mkValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode nft)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @CDPDatum @CDPActions

validatorScript :: CDPParams -> TScripts.Validator
validatorScript = TScripts.validatorScript . compiledValidator

validatorAddress :: CDPParams -> Ledger.Address
validatorAddress = Ledger.scriptAddress . validatorScript

type InitSchema = Contract.Endpoint "Init"     ()

type CDPSchema = Contract.Endpoint "Open"     EPT
    Contract..\/ Contract.Endpoint "Deposit"  EPT
    Contract..\/ Contract.Endpoint "Withdraw" EPT
    Contract..\/ Contract.Endpoint "Mint"     EPT
    Contract..\/ Contract.Endpoint "Burn"     EPT

getDatum :: PlutusTx.FromData b => Ledger.ChainIndexTxOut -> Maybe b
getDatum o = preview Ledger.ciTxOutDatum o >>= rightToMaybe >>= (PlutusTx.fromBuiltinData . Ledger.getDatum)

getValue :: Ledger.ChainIndexTxOut -> Ledger.Value
getValue = view Ledger.ciTxOutValue

aTokenName :: Value.TokenName
aTokenName = "iTSLA-AuthToken"

{-# INLINEABLE uMkPolicy #-}
uMkPolicy :: Value.AssetClass -> () -> Ledger.ScriptContext -> Bool
uMkPolicy nft _ ctx =
  PTrace.traceIfFalse "Input does not contain the real Manager" (inVal == (Value.assetClassValue nft 1)) &&
  PTrace.traceIfFalse "Only one auth token can only be minted at once" checkMintedAmount
  where
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
        
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    input :: Ledger.TxInInfo
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> PTrace.traceError "Expected exactly one script input"
      
    checkMintedAmount :: Bool
    checkMintedAmount = case (Value.flattenValue (Ledger.txInfoMint info)) of
      [(_, _, amt)] -> amt PL.== 1
      _             -> False
    
uMintingPolicy :: Value.AssetClass -> TScripts.MintingPolicy
uMintingPolicy nft =
  Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy . uMkPolicy ||])
    `PlutusTx.applyCode` PlutusTx.liftCode nft

uMintingPolicyHash :: Value.AssetClass -> Scripts.MintingPolicyHash
uMintingPolicyHash = Scripts.mintingPolicyHash . uMintingPolicy

uCurrencySymbol :: Value.AssetClass -> Value.CurrencySymbol
uCurrencySymbol = Value.mpsSymbol . uMintingPolicyHash

uTokenName :: Value.TokenName
uTokenName = "iTSLA-User-Atoken"

{-# INLINEABLE mkPolicy #-}
mkPolicy :: Value.AssetClass -> () -> Ledger.ScriptContext -> Bool
mkPolicy atk _ ctx = 
  PTrace.traceIfFalse "Input does not contain the real User's CDP" exactOneUser
  
  where 
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
    
    input :: Ledger.TxInInfo
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> PTrace.traceError "Expected exactly one script input"
            
    flattenVal :: [(Value.CurrencySymbol, Value.TokenName, Integer)]
    flattenVal = Value.flattenValue . Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    exactOneUser :: Bool
    exactOneUser = 
      let 
        isAtk :: (Value.CurrencySymbol, Value.TokenName, Integer) -> Bool
        isAtk (cs, tn, _) = atk PL.== (Value.assetClass cs tn) 
        xs = PL.filter isAtk flattenVal
      in 
        case xs of
          [_] -> True
          _ -> PTrace.traceError "Expected exactly one user input"

mintingPolicy :: Value.AssetClass -> TScripts.MintingPolicy
mintingPolicy atk =
  Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy . mkPolicy||])
    `PlutusTx.applyCode` PlutusTx.liftCode atk

mintingPolicyHash :: Value.AssetClass -> Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash . mintingPolicy

myCurrencySymbol :: Value.AssetClass -> Value.CurrencySymbol
myCurrencySymbol = Value.mpsSymbol . mintingPolicyHash

myTokenName :: Value.TokenName
myTokenName = "iTSLA"

containsAuthToken :: Value.AssetClass -> Ledger.ChainIndexTxOut -> Bool 
containsAuthToken nft o = valid $ getDatum @CDPDatum o
  where valid (Just (ManagerDatum _)) = Ledger._ciTxOutValue o == Value.assetClassValue nft 1
        valid _                       = False

containsMyKey :: Value.AssetClass -> Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
containsMyKey atk mk o = valid $ getDatum @CDPDatum o
  where valid (Just (UserDatum k _ _)) = k == mk && containsATK (Ledger._ciTxOutValue o) 
        valid _                        = False
        containsATK :: Value.Value -> Bool
        containsATK val = (length $ filter (\(a, b, c) -> Value.assetClass a b == atk && c == 1) (Value.flattenValue val)) > 0

openCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
openCDP EPT{..} = do
  managers <- M.filter (containsAuthToken getAToken) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myKey <- Contract.ownPubKeyHash 
  let (oref, o) = head $ M.toList managers
      mbUsers = getDatum @CDPDatum o
  case mbUsers of
    Just (ManagerDatum users) -> 
      void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
      where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                   <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                   <> Constraints.unspentOutputs (M.fromList [(oref, o)])
                   <> Constraints.mintingPolicy (uMintingPolicy getAToken)
            val     = Value.assetClassValue (Value.assetClass (uCurrencySymbol getAToken) uTokenName) 1
            tx      = Constraints.mustMintValue val
                   <> Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkOpen myKey)
                   <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users)) (getValue o)
                   <> Constraints.mustPayToTheScript (UserDatum myKey 0 0) (val <> Ada.lovelaceValueOf 0)
    _ -> Contract.throwError "List of users is not available"
                        
depositCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
depositCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter (containsAuthToken getAToken) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey getUToken myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do 
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum _) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
            where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                         <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                         <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                  tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkBalance getAmount)
                         <> Constraints.mustPayToTheScript (UserDatum myKey (lk + getAmount) mt) (getValue uo <> Ada.lovelaceValueOf getAmount) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

withdrawCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
withdrawCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter (containsAuthToken getAToken) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey getUToken myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum _) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
            where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                         <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                         <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                  tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkBalance (-getAmount))
                         <> Constraints.mustPayToTheScript (UserDatum myKey (lk - getAmount) mt) (getValue uo <> Ada.lovelaceValueOf (-getAmount)) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

mintCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
mintCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter (containsAuthToken getAToken) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey getUToken myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum _) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
            where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                         <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                         <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                         <> Constraints.mintingPolicy (mintingPolicy getUToken)
                  val = Value.assetClassValue (Value.assetClass (myCurrencySymbol getUToken) myTokenName) getAmount
                  tx      = Constraints.mustMintValue val
                         <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkToken getAmount)
                         <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt + getAmount)) (getValue uo)
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

burnCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
burnCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter (containsAuthToken getAToken) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey getUToken myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum _) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
            where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                         <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                         <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                         <> Constraints.mintingPolicy (mintingPolicy getUToken)
                  val     = Value.assetClassValue (Value.assetClass (myCurrencySymbol getUToken) myTokenName) (-getAmount)
                  tx      = Constraints.mustMintValue val
                         <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkToken (-getAmount))
                         <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt - getAmount)) (getValue uo)
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"
      
fromCurrencyError :: Currency.CurrencyError -> Contract.ContractError
fromCurrencyError = \case
  (Currency.CurContractError e) -> e

initOutput :: forall w s. Contract.Contract w s Contract.ContractError Value.AssetClass
initOutput = do
  mk <- Contract.ownPubKeyHash
  cs <- Contract.mapError fromCurrencyError $ Currency.currencySymbol <$> Currency.mintContract mk [(aTokenName, 1)] 
  let lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams p $ Value.assetClass (uCurrencySymbol p) uTokenName)
      p       = Value.assetClass cs aTokenName
      val     = Value.assetClassValue (Value.assetClass cs aTokenName) 1
      tx      = Constraints.mustPayToTheScript (ManagerDatum []) val
  void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
  return p

initEndpoint :: Contract.Contract (Last Value.AssetClass) InitSchema Contract.ContractError ()
initEndpoint = Contract.selectList [init'] <> initEndpoint
  where
    init'     = Contract.endpoint @"Init"     $ \_ -> Contract.handleError Contract.logError $ initOutput >>= Contract.tell . Last . Just

myEndpoints :: Contract.Contract () CDPSchema Contract.ContractError ()
myEndpoints = Contract.selectList [open', deposit', withdraw', mint', burn'] >> myEndpoints
  where   
    open'     = Contract.endpoint @"Open"     $ \a -> Contract.handleError Contract.logError $ openCDP a
    deposit'  = Contract.endpoint @"Deposit"  $ \a -> Contract.handleError Contract.logError $ depositCDP a
    withdraw' = Contract.endpoint @"Withdraw" $ \a -> Contract.handleError Contract.logError $ withdrawCDP a
    mint'     = Contract.endpoint @"Mint"     $ \a -> Contract.handleError Contract.logError $ mintCDP a
    burn'     = Contract.endpoint @"Burn"     $ \a -> Contract.handleError Contract.logError $ burnCDP a
 
main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  i1 <- Trace.activateContractWallet (knownWallet 1) initEndpoint
  o1 <- Trace.activateContractWallet (knownWallet 1) myEndpoints
  o2 <- Trace.activateContractWallet (knownWallet 2) myEndpoints

  Trace.callEndpoint @"Init" i1 ()
  void $ Trace.waitNSlots 1

  p <- getCDPParam i1
  let u = Value.assetClass (uCurrencySymbol p) uTokenName
  
  Trace.callEndpoint @"Open" o1 $ EPT p u 0
  void $ Trace.waitNSlots 3

  Trace.callEndpoint @"Deposit" o1 $ EPT p u 1000
  void $ Trace.waitNSlots 3
  
  Trace.callEndpoint @"Deposit" o2 $ EPT p u 1000
  void $ Trace.waitNSlots 3
   
  Trace.callEndpoint @"Open" o2 $ EPT p u 0
  void $ Trace.waitNSlots 3

  Trace.callEndpoint @"Withdraw" o1 $ EPT p u 500
  void $ Trace.waitNSlots 3  
  
  Trace.callEndpoint @"Burn" o1 $ EPT p u 10
  void $ Trace.waitNSlots 3  

  Trace.callEndpoint @"Mint" o1 $ EPT p u 1
  void $ Trace.waitNSlots 3  

  where
    getCDPParam :: Trace.ContractHandle (Last Value.AssetClass) InitSchema Contract.ContractError -> Trace.EmulatorTrace Value.AssetClass
    getCDPParam h = do
      Trace.observableState h >>= \case
        Last (Just p) -> return p
        Last _        -> Trace.waitNSlots 1 >> getCDPParam h 
        
