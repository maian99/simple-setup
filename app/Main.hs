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
import qualified PlutusTx.Eq as PEq
import qualified PlutusTx.List as PList
import qualified PlutusTx.Numeric as PNum
import qualified PlutusTx.Ord as POrd
import qualified PlutusTx.Trace as PTrace