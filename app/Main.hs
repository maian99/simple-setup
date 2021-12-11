{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

module Main where

import Control.Monad (void)
import Control.Lens
import qualified Data.Map as M
import Data.Aeson (FromJSON, ToJSON)
import Data.Either.Combinators (rightToMaybe)
import Data.Monoid (Last (Last))
import GHC.Generics
import qualified Ledger
import qualified Ledger.Ada as Ada
import qualified Ledger.Constraints as Constraints
import qualified Plutus.Contract as Contract
import qualified Plutus.Contracts.Currency as Currency
import qualified Ledger.Scripts as Scripts
import qualified Ledger.Typed.Scripts as TScripts
import qualified Ledger.Value as Value
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import qualified PlutusTx.Trace as PTrace
import Wallet.Emulator (knownWallet)

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

data Open = Open Ledger.PubKeyHash
data Deposit = Deposit Ledger.PubKeyHash Integer
data Withdraw = Withdraw Ledger.PubKeyHash Integer
data Mint = Mint Ledger.PubKeyHash Integer
data Burn = Burn Ledger.PubKeyHash Integer

data CDPActions 
  = MkOpen Open 
  | MkDeposit Deposit 
  | MkWithdraw Withdraw 
  | MkMint Mint
  | MkBurn Burn

PlutusTx.unstableMakeIsData ''CDPActions
PlutusTx.unstableMakeIsData ''CDPDatum
PlutusTx.unstableMakeIsData ''CDPParams
PlutusTx.unstableMakeIsData ''EPT
PlutusTx.unstableMakeIsData ''Open
PlutusTx.unstableMakeIsData ''Deposit
PlutusTx.unstableMakeIsData ''Withdraw
PlutusTx.unstableMakeIsData ''Mint
PlutusTx.unstableMakeIsData ''Burn
PlutusTx.makeLift ''CDPParams

instance TScripts.ValidatorTypes CDP where
  type DatumType CDP = CDPDatum
  type RedeemerType CDP = CDPActions

{-# INLINEABLE mkValidator #-}
mkValidator :: CDPParams -> CDPDatum -> CDPActions -> Ledger.ScriptContext -> Bool
mkValidator CDPParams{..} d a ctx = 
  case a of 
    MkOpen (Open k) -> 
      PTrace.traceIfFalse "Inputs do not contain the real Manager" (inVal == nftVal) &&
      PTrace.traceIfFalse "Wrong signature" (Ledger.txSignedBy info k) -- &&
--      PTrace.traceIfFalse
    MkDeposit (Deposit k a) -> True
    MkWithdraw (Withdraw k a) -> True
    MkMint (Mint k a) -> True
    MkBurn (Burn k a) -> True
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
            _   -> PTrace.traceError "expected exactly one script input"
            
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    nftVal :: Value.Value
    nftVal = (Value.assetClassValue ogetAToken 1)
    
    atkVal :: Value.Value
    atkVal = (Value.assetClassValue ogetUToken 1)
      
    ownOutput :: [Ledger.TxOut]
    ownOutput = Ledger.getContinuingOutputs ctx
    
    ownInput :: Ledger.TxOut
    ownInput = case Ledger.findOwnInput ctx of
      Nothing -> PTrace.traceError "Expected input"
      Just i -> Ledger.txInInfoResolved i
    
    ownManagerOutput :: Ledger.TxOut
    ownManagerOutput = case filter isManager ownOutput of
      [o] -> o
      _   -> PTrace.traceError "Expected exactly one Manager output"
    
    outUserOutput :: Ledger.TxOut
    outUserOutput = case filter isUser ownOutput of
      [o] -> o
      _   -> PTrace.traceError "Expected exactly one User output"
      
    outManagerDatum :: CDPDatum
    outManagerDatum = case cdpDatum ownManagerOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> PTrace.traceError "Impossible case"

    inManagerDatum :: CDPDatum
    inManagerDatum = case cdpDatum d (`Ledger.findDatum` info) of
      Just a -> a
      _ -> PTrace.traceError "Not manager datum"
    
    
    ownUserDatum :: CDPDatum
    ownUserDatum = case cdpDatum ownUserOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> PTrace.traceError "Impossible case"
    
    managerDatumList :: Ledger.PubKeyHash -> Bool
    managerDatumList k = case inManagerDatum of
      ManagerDatum l -> 
        case outManagerDatum of
          ManagerDatum (a:as) -> a == k && l == as
          _ -> PTrace.traceError "Invalid manager output datum"
      _ -> PTrace.traceError "Wrong manager input datum"
    
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
      Scripts.Datum d <- f dh
      PlutusTx.fromBuiltinData d
    

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
uMkPolicy :: () -> Ledger.ScriptContext -> Bool
uMkPolicy _ _ = True

uMintingPolicy :: TScripts.MintingPolicy
uMintingPolicy =
  Ledger.mkMintingPolicyScript
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy uMkPolicy||])

uMintingPolicyHash :: Scripts.MintingPolicyHash
uMintingPolicyHash = Scripts.mintingPolicyHash uMintingPolicy

uCurrencySymbol :: Value.CurrencySymbol
uCurrencySymbol = Value.mpsSymbol uMintingPolicyHash

uTokenName :: Value.TokenName
uTokenName = "iTSLA-User-Atoken"

{-# INLINEABLE mkPolicy #-}
mkPolicy :: () -> Ledger.ScriptContext -> Bool
mkPolicy _ _ = True
{-
  PTrace.traceIfFalse "Wrong amount minted" checkMintedAmount
  where 
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
    
    hasUTxO :: Bool
    hasUTxO any (\i -> Ledger.txInInfoOutRef i == utxo) $ txInfoInputs info
    
    checkMintedAmount :: Bool
    checkMintedAmount case flattenValue (Ledger.txInfoMint info) of
      [(_, tn', amt)] -> tn' == tn && amt == 1
      _               -> False
-}

mintingPolicy :: TScripts.MintingPolicy
mintingPolicy =
  Ledger.mkMintingPolicyScript
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy mkPolicy||])

mintingPolicyHash :: Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash mintingPolicy

myCurrencySymbol :: Value.CurrencySymbol
myCurrencySymbol = Value.mpsSymbol mintingPolicyHash

myTokenName :: Value.TokenName
myTokenName = "iTSLA"

containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
containsAuthToken o = valid $ getDatum @CDPDatum o
  where valid (Just (ManagerDatum _)) = True
        valid _                       = False

containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
containsMyKey mk o = valid $ getDatum @CDPDatum o
  where valid (Just (UserDatum k _ _)) = True
        valid _                        = False

adaPrice :: Double
adaPrice = 1.2

iTSLAPrice :: Double
iTSLAPrice = 709.6

collateralRatio :: Double
collateralRatio = 1.5

maintainRatio :: Integer -> Integer -> Bool
maintainRatio lk mt = adaPrice * (fromIntegral lk) >= collateralRatio * iTSLAPrice * 1000000.0 * (fromIntegral mt)

openCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
openCDP EPT{..} = do
  managers <- M.filter containsAuthToken <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myKey <- Contract.ownPubKeyHash 
  let (oref, o) = head $ M.toList managers
      mbUsers = getDatum @CDPDatum o
  case mbUsers of
    Just (ManagerDatum users) -> 
      if myKey `elem` users then Contract.throwError "This user has already openned a CDP"  
      else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
           where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                        <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                        <> Constraints.unspentOutputs (M.fromList [(oref, o)])
                        <> Constraints.mintingPolicy uMintingPolicy
                 val     = Value.assetClassValue (Value.assetClass uCurrencySymbol uTokenName) 1
                 tx      = Constraints.mustMintValue val
                        <> Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkOpen $ Open myKey)
                        <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users)) (getValue o)
                        <> Constraints.mustPayToTheScript (UserDatum myKey 0 0) val
    _ -> Contract.throwError "List of users is not available"
                        
depositCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
depositCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP@@"
   else do 
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP@@@@"
            else if getAmount < 0 then Contract.throwError "Cannot deposit negative amount"
            else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                 where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                              <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                              <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                       tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkDeposit $ Deposit myKey getAmount)
                              <> Constraints.mustPayToTheScript (UserDatum myKey (lk + getAmount) mt) (getValue uo <> Ada.lovelaceValueOf getAmount) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

withdrawCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
withdrawCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
            else if getAmount < 0 then Contract.throwError "Cannot withdraw negative amount"
            else if ((Ada.fromValue $ getValue uo) < Ada.lovelaceOf getAmount) then Contract.throwError "The withdrawal amount exceeds the locked value" 
            else if not $ maintainRatio (lk - getAmount) mt then Contract.throwError "The withdrawal amount breaks the ratio"
                 else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                      where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                                   <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                                   <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                            tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkWithdraw $ Withdraw myKey getAmount)
                                   <> Constraints.mustPayToTheScript (UserDatum myKey (lk - getAmount) mt) (getValue uo <> Ada.lovelaceValueOf (-getAmount)) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

mintCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
mintCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP" 
            else if getAmount < 0 then Contract.throwError "Cannot mint negative amount"
            else if not $ maintainRatio lk (mt + getAmount) then Contract.throwError "The minting amount breaks the ratio"
            else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                 where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                              <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                              <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                              <> Constraints.mintingPolicy mintingPolicy
                       val = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) getAmount
                       tx      = Constraints.mustMintValue val
                              <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkMint $ Mint myKey getAmount)
                              <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt + getAmount)) (getValue uo)
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

burnCDP :: EPT -> Contract.Contract w s Contract.ContractError ()
burnCDP EPT{..} = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt (validatorAddress $ CDPParams getAToken getUToken)
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
            else if getAmount < 0 then Contract.throwError "Cannot burn negative amount" 
            else if (getAmount > mt) then Contract.throwError "The amount exceeds the current maximal burning size"
            else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                 where lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams getAToken getUToken)
                              <> Constraints.otherScript (validatorScript $ CDPParams getAToken getUToken)
                              <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                              <> Constraints.mintingPolicy mintingPolicy
                       val     = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) (-getAmount)
                       tx      = Constraints.mustMintValue val
                              <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData $ MkBurn $ Burn myKey getAmount)
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
  let lookups = Constraints.typedValidatorLookups (compiledValidator $ CDPParams p $ Value.assetClass uCurrencySymbol uTokenName)
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
  let u = Value.assetClass uCurrencySymbol uTokenName
  
  Trace.callEndpoint @"Open" o1 $ EPT p u 0
  void $ Trace.waitNSlots 1

  where
    getCDPParam :: Trace.ContractHandle (Last Value.AssetClass) InitSchema Contract.ContractError -> Trace.EmulatorTrace Value.AssetClass
    getCDPParam h = do
      Trace.observableState h >>= \case
        Last (Just p) -> return p
        Last _        -> Trace.waitNSlots 1 >> getCDPParam h 
        
