{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib
  ( reunion,
    showPeople,
  )
where

import Control.Monad
import Data.Char
import Data.Foldable
import qualified Data.List 
import Data.SBV
import Data.SBV.Control
import Data.SBV.Maybe hiding (map)
import Data.Traversable

-- | Helper functor
newtype Const a = Const a

-- | Roles
data Role = Culprit | Bystander

-- | Sexes
data Sex = Man | Woman

-- | Rooms
data Room = One | Two | Three

-- | Wolfgang
data Wolfgang = Wolfgang | NotWolfgang

mkSymbolicEnumeration ''Role
mkSymbolicEnumeration ''Sex
mkSymbolicEnumeration ''Room
mkSymbolicEnumeration ''Wolfgang

data Person f = Person
  { nm :: String,
    sex :: f Sex,
    roleOne :: f Role,
    roleTwo :: f Role,
    roleThree :: f Role,
    apparentlyDied :: f (Maybe Room),
    wolfgang :: f (Wolfgang)
  }

newPerson :: String -> Symbolic (Person SBV)
newPerson n = Person n <$> free_ <*> free_ <*> free_ <*> free_ <*> free_ <*> free_

-- | Get the concrete value of the person in the model
getPerson :: Person SBV -> Query (Person Const)
getPerson Person {nm, sex, roleOne, roleTwo, roleThree, apparentlyDied, wolfgang} =
  Person nm
    <$> (Const <$> getValue sex)
    <*> (Const <$> getValue roleOne)
    <*> (Const <$> getValue roleTwo)
    <*> (Const <$> getValue roleThree)
    <*> (Const <$> getValue apparentlyDied)
    <*> (Const <$> getValue wolfgang)

showPeople :: [Person Const] -> String
showPeople people =
  let (culprits1, culprits2, culprits3, bystanders) = categories
   in Data.List.dropWhileEnd isSpace $
        unlines $
          ["Culprits (room 1):"]
            <> fmap nm' culprits1
            <> ["Culprits (room 2):"]
            <> fmap nm' culprits2
            <> ["Culprits (room 3):"]
            <> fmap nm' culprits3
            <> ["Bystanders:"]
            <> fmap nm' bystanders
  where
    nm' = ("  " <>) . nm
    categories :: ([Person Const], [Person Const], [Person Const], [Person Const])
    categories =
      ( filter culprit1 people,
        filter culprit2 people,
        filter culprit3 people,
        filter (\person -> not (culprit1 person || culprit2 person || culprit3 person)) people
      )
      where
        culprit1 (Person _ _ (Const Culprit) _ _ _ _) = True
        culprit1 _ = False
        culprit2 (Person _ _ _ (Const Culprit) _ _ _) = True
        culprit2 _ = False
        culprit3 (Person _ _ _ _ (Const Culprit) _ _) = True
        culprit3 _ = False

reunion :: IO ([Person Const])
reunion = runSMT $ do
  -- Characters
  simone <- person "Simone Montleib" sWoman Nothing
  wolfgang <- person "Wolfgang Wehrhardt" sMan (Just sOne)
  princessa <- person "Princessa Traptenkastel" sWoman (Just sOne)
  lance <- person "Lance Goldenhope" sMan (Just sOne)
  hattie <- person "Hattie Gizmo" sWoman (Just sTwo)
  gizmo <- person "Professor Gizmo" sMan (Nothing)
  alouette <- person "Alouette Criminale" sWoman (Just sThree)
  vince <- person "Vince Criminale" sMan (Just sTwo)
  grincella <- person "Grincella Disagreeabella" sWoman (Nothing)
  frendley <- person "Frendley Kindman" sMan (Nothing)

  let people = [simone, wolfgang, princessa, lance, hattie, gizmo, alouette, vince, grincella, frendley]

  -- Round 1
  murder One people [wolfgang, lance, princessa] alouette lance vince
  vouch One [gizmo, hattie]
  vouch One [vince, alouette]
  vouch One [grincella, frendley]
  inspectBody hattie wolfgang
  inspectBody alouette lance
  inspectBody grincella princessa

  -- Round 2
  murder Two people [hattie, vince] alouette lance vince
  vouch Two [simone, grincella, alouette]
  vouch Two [gizmo, frendley]
  inspectBody gizmo hattie
  inspectBody frendley vince
  constrain $ purple gizmo (roleTwo vince .== sBystander)
  
  constrain $ bystander gizmo

  -- Round 3
  murder Three people [alouette] alouette lance vince
  vouch Three [simone, frendley]
  vouch Three [grincella, gizmo]
  inspectBody simone alouette

  query $ do
    cs <- checkSat
    case cs of
      Sat -> do
        for people (getPerson)
      _ -> error $ "Solver said: " ++ show cs
  where
    person name theirSex whenDied = do
      p <- newPerson name
      constrain $ sex p .== theirSex
      constrain $ wolfgang p .== (if name == "Wolfgang Wehrhardt" then sWolfgang else sNotWolfgang)
      constrain $ apparentlyDied p .== (liftMaybe whenDied)
      pure p

    roomToRole One = roleOne
    roomToRole Two = roleTwo
    roomToRole Three = roleThree
    liftRoom One = sOne
    liftRoom Two = sTwo
    liftRoom Three = sThree

    {- Every victim must apparently die in the room they die in, and nobody else can die in that room
       And the number of culprits for that room must be greater than one and less than the number of victims who aren't culprits -}
    murder room people victims alouette lance vince = do
      for_ victims (\victim -> constrain $ apparentlyDied victim .== (liftMaybe $ Just (liftRoom room)))
      constrain $ culpritsForRoom .>= 1
      constrain $ culpritsForRoom .<= trueVictimsForRoom
      constrain $ purple alouette (purple lance (needAManToKillAMan))
      when vinceAppearsToBeVictim $ constrain $ purple vince (nonWolfgangCulprits .>= 1)
      where
        role = roomToRole room
        trueVictimsForRoomF f = (sum (map (\victim -> oneIf (bystander victim .&& f victim)) victims)) :: SWord8
        trueVictimsForRoom = trueVictimsForRoomF $ \_ -> sTrue
        culpritsForRoomF f = (sum (map (\p -> oneIf $ (role p .== sCulprit .&& (f p))) people) :: SWord8)
        culpritsForRoom = culpritsForRoomF $ \_ -> sTrue
        maleCulpritsForRoom = culpritsForRoomF $ \c -> sex c .== sMan
        maletrueVictimsForRoom = trueVictimsForRoomF $ \victim -> sex victim .== sMan
        needAManToKillAMan = ite (maletrueVictimsForRoom .>= 1) (maleCulpritsForRoom .>= 1) sTrue
        vinceAppearsToBeVictim = Data.List.any (\victim -> nm victim == nm vince) victims
        nonWolfgangCulprits = culpritsForRoomF $ \c -> wolfgang c .== sNotWolfgang

    {- s must be true if a bystander says it, otherwise it could be false -}
    purple p s = ite (bystander p) s sTrue

    {- if the inspector is a bystander, the victim is a bystander (and they better be dead)  -}
    inspectBody inspector victim = constrain $ purple inspector (bystander victim)

    pairs l =
      let unmirrored_pairs = [(x, y) | (x : ys) <- Data.List.tails l, y <- ys]
       in unmirrored_pairs <> fmap (\(x, y) -> (y, x)) unmirrored_pairs
    vouch room people = for_ (pairs people) (\(voucher, vouchee) -> constrain $ purple voucher ((roomToRole room) vouchee .== sBystander))

    culprit p = roleOne p .== sCulprit .|| roleTwo p .== sCulprit .|| roleThree p .== sCulprit
    bystander = sNot . culprit
