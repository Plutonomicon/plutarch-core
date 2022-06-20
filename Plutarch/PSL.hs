{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.PSL where
  
import Data.Kind (Type)
import Plutarch.EType
import Plutarch.Core
import GHC.Generics (Generic)
import qualified MonoidDo
import Data.Proxy (Proxy (Proxy))

data EInteger (ef :: ETypeF)
instance EIsNewtype EInteger where type EIsNewtype' _ = False

data EValue (ef :: ETypeF)
instance EIsNewtype EValue where type EIsNewtype' _ = False

data EUTXO (ef :: ETypeF)
instance EIsNewtype EUTXO where type EIsNewtype' _ = False

data EUTXORef (ef :: ETypeF)
instance EIsNewtype EUTXORef where type EIsNewtype' _ = False

data ETokenName (ef :: ETypeF)
instance EIsNewtype ETokenName where type EIsNewtype' _ = False

data ECurrencySymbol (ef :: ETypeF)
instance EIsNewtype ECurrencySymbol where type EIsNewtype' _ = False

data ETimeRange (ef :: ETypeF)
instance EIsNewtype ETimeRange where type EIsNewtype' _ = False

data EPubKeyHash (ef :: ETypeF)
instance EIsNewtype EPubKeyHash where type EIsNewtype' _ = False

data EAddress (ef :: ETypeF)
instance EIsNewtype EAddress where type EIsNewtype' _ = False

data EDCert (ef :: ETypeF)
instance EIsNewtype EDCert where type EIsNewtype' _ = False

data EByteString (ef :: ETypeF)
instance EIsNewtype EByteString where type EIsNewtype' _ = False

type EFix :: (EType -> EType) -> EType
newtype EFix f ef = EFix (Ef ef (f (EFix f)))
instance EIsNewtype (EFix f) where type EIsNewtype' _ = False

data EListF a self ef
  = ENil
  | ECons (Ef ef a) (Ef ef self)
  deriving stock Generic
  deriving anyclass EIsNewtype

newtype EList a ef = EList (Ef ef (EFix (EListF a)))
  deriving stock Generic
  deriving anyclass EIsNewtype

data EData (ef :: ETypeF)
  = EDataConstr (Ef ef EInteger) (Ef ef (EList EData))
  | EDataMap (Ef ef (EList (EPair EData EData)))
  | EDataList (Ef ef (EList EData))
  | EDataInteger (Ef ef EInteger)
  | EDataByteString (Ef ef EByteString)
instance EIsNewtype EData where type EIsNewtype' _ = False

data EOwnUTXO d f = EOwnUTXO
  { value :: Ef f EValue
  , datum :: Ef f d
  }
  deriving stock Generic
  deriving anyclass EIsNewtype

data Undefined = Undefined

data EDiagram (datumType :: EType) (ef :: ETypeF)
instance EIsNewtype (EDiagram d) where type EIsNewtype' _ = False

class IsEType' edsl a => IsETypeHelper edsl a
instance IsEType' edsl a => IsETypeHelper edsl a

class EConstructable' edsl a => EConstructableHelper edsl a
instance EConstructable' edsl a => EConstructableHelper edsl a

class (forall a. EConstructable edsl a => EConstructable edsl (f a)) => EConstructable2 edsl f
instance (forall a. EConstructable edsl a => EConstructable edsl (f a)) => EConstructable2 edsl f

class
  ( forall d. Monoid (Term edsl (EDiagram d))
  , (forall d. IsEType edsl d => IsETypeHelper edsl (MkETypeRepr (EDiagram d)))
  , Monoid (Term edsl EValue)
  , EDSL edsl
  , ESOP edsl
  , IsEType' edsl (MkETypeRepr EInteger)
  , forall f. EConstructable2 edsl f => EConstructableHelper edsl (MkETypeRepr (EFix f))
  , IsEType' edsl (MkETypeRepr EValue)
  , IsEType' edsl (MkETypeRepr EUTXO)
  , IsEType' edsl (MkETypeRepr EUTXORef)
  , IsEType' edsl (MkETypeRepr ETokenName)
  , IsEType' edsl (MkETypeRepr ECurrencySymbol)
  , IsEType' edsl (MkETypeRepr ETimeRange)
  , IsEType' edsl (MkETypeRepr EPubKeyHash)
  , IsEType' edsl (MkETypeRepr EAddress)
  , IsEType' edsl (MkETypeRepr EDCert)
  , EConstructable' edsl (MkETypeRepr EData)
  ) => EPSL edsl where
  requireInput :: Term edsl EUTXORef -> Term edsl (EDiagram d)
  requireOwnInput :: Term edsl (EOwnUTXO d) -> Term edsl (EDiagram d)
  createOwnOutput :: Term edsl (EOwnUTXO d) -> Term edsl (EDiagram d)
  witnessOutput :: Term edsl EUTXO -> Term edsl (EDiagram d)
  createOutput :: Term edsl EUTXO -> Term edsl (EDiagram d)
  mintOwn :: Term edsl ETokenName -> Term edsl EInteger -> Term edsl (EDiagram d)
  witnessMint :: Term edsl ECurrencySymbol -> Term edsl ETokenName -> Term edsl EInteger -> Term edsl (EDiagram d)
  requireSignature :: Term edsl EPubKeyHash -> Term edsl (EDiagram d)
  requireValidRange :: Term edsl ETimeRange -> Term edsl (EDiagram d)
  requireDCert :: Term edsl EDCert -> Term edsl (EDiagram f)
  toProtocol :: Protocol p d => Proxy p -> Term edsl d -> Term edsl EValue -> Term edsl EUTXO
  toAddress :: Term edsl EAddress -> Term edsl EValue -> Term edsl EData -> Term edsl EUTXO
  fromPkh :: Term edsl EPubKeyHash -> Term edsl EAddress
  utxoRefIs :: Term edsl EUTXORef -> Term edsl EUTXO -> Term edsl (EDiagram d)
  emptyValue :: Term edsl EValue
  mkValue :: Term edsl ECurrencySymbol -> Term edsl ETokenName -> Term edsl EInteger -> Term edsl EValue
  mkAda :: Term edsl EInteger -> Term edsl EValue
  mkOwnValue :: Term edsl ETokenName -> Term edsl EInteger

data Specification d where
  Specification ::
    forall d (caseType :: EType).
    (forall edsl.
      EPSL edsl =>
      Term edsl caseType ->
      Term edsl (EDiagram d)
    ) -> Specification d

class Protocol p d | p -> d where
  specification :: Proxy p -> Specification d

data ENat f = EZ | ES (Ef f ENat)
  deriving stock Generic
  deriving anyclass EIsNewtype

instance EConstructable edsl ENat => Num (Term edsl ENat) where
  fromInteger 0 = econ EZ
  fromInteger n | n > 0 = econ $ ES (fromInteger n)
  fromInteger _ = error "negative"

paymentCases :: EPSL edsl => Term edsl EPubKeyHash -> Term edsl (EDiagram EPubKeyHash)
paymentCases pkh = requireSignature pkh

data PaymentProtocol
instance Protocol PaymentProtocol EPubKeyHash where
  specification _ = Specification @EPubKeyHash @EPubKeyHash paymentCases

--class Implements i p | i -> p where

data CounterDatum f = CounterDatum
  { counter :: Ef f ENat
  , addr :: Ef f EAddress
  , datum :: Ef f EData
  }
  deriving stock Generic
  deriving anyclass EIsNewtype

data CounterCase f where
  CounterStep :: Ef f CounterDatum -> Ef f EValue -> CounterCase f
  CounterConsume :: Ef f EAddress -> Ef f EData -> Ef f EValue -> CounterCase f
  deriving stock Generic
  deriving anyclass EIsNewtype

counterCases :: EPSL edsl => Term edsl CounterCase -> Term edsl (EDiagram CounterDatum)
counterCases c = ematch c \case
  CounterStep datum' value ->
    ematch datum' \datum@(CounterDatum counter _ _) ->
    MonoidDo.do
      requireOwnInput $ econ $ EOwnUTXO value (econ $ datum { counter = econ $ ES counter })
      createOwnOutput $ econ $ EOwnUTXO value (econ $ datum)
  CounterConsume addr outdatum value -> MonoidDo.do
    requireOwnInput $ econ $ EOwnUTXO value (econ $ CounterDatum { counter = econ EZ, addr, datum = outdatum })
    createOutput $ toAddress addr value outdatum

data CounterProtocol
instance Protocol CounterProtocol CounterDatum where
  specification _ = Specification @CounterDatum @CounterCase counterCases

data ExampleDatum ef = ExampleDatum (Ef ef EPubKeyHash)
  deriving stock Generic
  deriving anyclass EIsNewtype

data ExampleCase ef where
  ExampleConsume ::
    Ef ef ENat ->
    Ef ef EValue ->
    Ef ef EValue ->
    Ef ef EPubKeyHash ->
    Ef ef EUTXORef ->
    ExampleCase ef
  deriving stock Generic
  deriving anyclass EIsNewtype

exampleCases :: EPSL edsl => Term edsl ExampleCase -> Term edsl (EDiagram ExampleDatum)
exampleCases c = ematch c \case
  ExampleConsume counter value' value pkh otherinput -> MonoidDo.do
    requireOwnInput $ econ $ EOwnUTXO value (econ $ ExampleDatum pkh)
    requireInput $ otherinput
    utxoRefIs otherinput $ toProtocol (Proxy @CounterProtocol) (econ $ CounterDatum counter (fromPkh pkh) undefined) value'
    --observeOutput $ undefined (canonical $ Proxy @CounterProtocol) value' (econ $ CounterDatum 5 pkh)

data MaksDatum f = MaksA | MaksB
  deriving stock Generic
  deriving anyclass EIsNewtype

data MaksCase ef where
  -- given one A, we produce an A and a B
  MaksFork :: { ada :: Ef ef EInteger, ada' :: Ef ef EInteger } -> MaksCase ef
  -- given one A and one B, we lock the value of both into the counter protocol
  MaksConsume :: { ada :: Ef ef EInteger, ada' :: Ef ef EInteger } -> MaksCase ef
  deriving stock Generic
  deriving anyclass EIsNewtype

pkh :: Term edsl EPubKeyHash
pkh = undefined

maksCases :: forall edsl. EPSL edsl => Term edsl MaksCase -> Term edsl (EDiagram MaksDatum)
maksCases c = ematch c \case
  MaksFork { ada, ada' } -> MonoidDo.do
    requireOwnInput $ econ $ EOwnUTXO (mkAda ada) (econ MaksA)
    createOwnOutput $ econ $ EOwnUTXO (mkAda ada) (econ MaksA)
    createOwnOutput $ econ $ EOwnUTXO (mkAda ada') (econ MaksB)
  MaksConsume { ada, ada' } -> MonoidDo.do
    requireOwnInput $ econ $ EOwnUTXO (mkAda ada) (econ MaksA)
    requireOwnInput $ econ $ EOwnUTXO (mkAda ada') (econ MaksB)
    createOutput $ toProtocol (Proxy @CounterProtocol) (econ $ CounterDatum 100 (fromPkh pkh) (econ $ EDataList $ econ $ EList $ econ $ EFix $ econ ENil)) (mkAda ada <> mkAda ada')

data MaksProtocol
instance Protocol MaksProtocol MaksDatum where
  specification _ = Specification @MaksDatum @MaksCase maksCases
