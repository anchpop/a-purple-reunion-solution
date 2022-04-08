{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import qualified Data.Maybe
import Data.SBV
import Data.SBV.Control
import Data.SBV.Maybe hiding (map)
import Data.Traversable
import qualified Debug.Trace

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
    isWolfgang :: f (Wolfgang)
  }

newPerson :: String -> Symbolic (Person SBV)
newPerson n = Person n <$> free_ <*> free_ <*> free_ <*> free_ <*> free_ <*> free_

-- | Get the concrete value of the person in the model
getPerson :: Person SBV -> Query (Person Const)
getPerson Person {nm, sex, roleOne, roleTwo, roleThree, apparentlyDied, isWolfgang} =
  Person nm
    <$> (Const <$> getValue sex)
    <*> (Const <$> getValue roleOne)
    <*> (Const <$> getValue roleTwo)
    <*> (Const <$> getValue roleThree)
    <*> (Const <$> getValue apparentlyDied)
    <*> (Const <$> getValue isWolfgang)

showPeople :: [Person Const] -> String
showPeople people =
  let (culprits1, culprits2, culprits3, bystanders) = categories
   in Data.List.dropWhileEnd isSpace $
        unlines $
          ["Culprits (room 1: " <> deathsInRoom One <> "):"]
            <> Data.List.sort (fmap nm' culprits1)
            <> ["Culprits (room 2: " <> deathsInRoom Two <> "):"]
            <> Data.List.sort (fmap nm' culprits2)
            <> ["Culprits (room 3: " <> deathsInRoom Three <> "):"]
            <> Data.List.sort (fmap nm' culprits3)
            <> ["Bystanders:"]
            <> Data.List.sort (fmap nm' bystanders)
  where
    nm' = ("  " <>) . nm
    deathsInRoom room = (Data.List.intercalate ", " . Data.List.sort $ Data.Maybe.mapMaybe (\Person {nm, apparentlyDied=Const apparentlyDied} -> if apparentlyDied == (Just room) then Just nm else Nothing) people)
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
  setOption $ ProduceUnsatCores True
  setOption $ OptionKeyword ":smt.core.minimize" ["true"]
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
  murder One people [wolfgang, lance, princessa] [[gizmo, hattie], [vince, alouette], [grincella, frendley]] alouette lance vince hattie gizmo wolfgang
  inspectBody One hattie wolfgang
  inspectBody One alouette lance
  inspectBody One grincella princessa

  -- Round 2
  murder Two people [hattie, vince] [[simone, grincella, alouette], [gizmo, frendley]] alouette lance vince hattie gizmo wolfgang
  inspectBody Two gizmo hattie
  inspectBody Two frendley vince
  namedConstraint (unwords [nm gizmo, "says", nm vince, "can't have killed hattie on room 2"]) $ purple gizmo (roleTwo vince .== sBystander)

  -- Round 3
  murder Three people [alouette] [[simone, frendley], [grincella, gizmo]] alouette lance vince hattie gizmo wolfgang
  inspectBody Three simone alouette

  -- test
  -- constrain $ bystander grincella 

  query $ do
    cs <- checkSat
    case cs of
      Sat -> do
        for people (getPerson)
      _ -> do 
        unsatCore <- getUnsatCore
        error $ unlines ["Solver said: " <> show cs, "Unsatisfiable constraints:", show unsatCore]
  where
    person name theirSex whenDied = do
      p <- newPerson name
      constrain $ sex p .== theirSex
      constrain $ isWolfgang p .== (if name == "Wolfgang Wehrhardt" then sWolfgang else sNotWolfgang)
      constrain $ apparentlyDied p .== (liftMaybe whenDied)
      pure p

    roomToRole One = roleOne
    roomToRole Two = roleTwo
    roomToRole Three = roleThree
    liftRoom One = sOne
    liftRoom Two = sTwo
    liftRoom Three = sThree

    murder room people victims alibiSets alouette lance vince hattie gizmo wolfgang = do
      for_ alibiSets (\alibiSet -> vouch room alibiSet)
      -- Every victim must apparently die in the room they die in
      for_ victims (\victim -> constrain $ apparentlyDied victim .== (liftMaybe $ Just (liftRoom room)))
      for_ (filter (\p -> not (nm p `elem` map nm victims)) people) (\victim -> constrain $ apparentlyDied victim ./= (liftMaybe $ Just (liftRoom room)))

      -- And the number of culprits for that room must be greater than or equal to one
      -- and less than or equal to the number of victims who aren't culprits
      constrain $ culpritsForRoom .>= 1
      constrain $ culpritsForRoom .<= trueVictimsForRoom

      --And if neither alouette and lance are culprits, there must be at least one man involevd in any
      --murder of a man
      namedConstraint (unwords ["for room", show room, nm alouette, "says that", nm lance, "says that only a man can kill a man"]) $ purple alouette (purple lance (haveAManToKillAMan))

      -- And if vince is the victim and not a culprit, wolfgang can't have killed him
      when vinceAppearsToBeVictim . namedConstraint (unwords [nm vince, "says", nm wolfgang, "can't kill him"]) $ purple vince (nonWolfgangCulprits .>= 1)

      -- And every true victim must have exactly one person who could have killed them
      for_
        victims
        ( \v ->
            ( namedConstraint (nm v <> " has only one killer")  $
              -- if the victim is a bystander, i.e. if they really died
              Debug.Trace.traceShow (nm v) $ (bystander v)
                `implies`
                ((allCulpritsF
                  ( \c ->
                      -- Could culprit c have killed victim v?
                      -- you can't kill youreslf
                      if nm c == nm v then sFalse else
                        ( observe (nm c <> " could have killed " <> nm v <> "?") $ sAll
                            id
                            [ -- A woman can't kill a man, if alouette and lance are to be believed
                              purple alouette (purple lance (sNot (sex v .== sMan .&& sex c .== sWoman))),
                              -- and if vince is a victim, wolfgang can't have killed him
                              (if nm v == nm vince && nm c == nm wolfgang then sFalse else sTrue),
                              -- and the killer cannot have an alibi that includes someone who isn't a culprit
                              -- so let's get everyone who guarantees their alibi for this murder, and check they're all culprits
                              let guarantours = join . Data.Maybe.mapMaybe (\alibiSet -> if (nm c `elem` map nm alibiSet) then Just (filter (\g -> nm g /= nm c) $ alibiSet) else Nothing) $ alibiSets
                              in Debug.Trace.traceShow (nm c, room, map nm guarantours) $ sAll culprit guarantours,
                              -- also, gizmo says in room 2 that vince did not kill hattie
                              if room == Two && nm c == nm vince && nm v == nm hattie then purple gizmo sFalse else sTrue
                            ]
                        )
                  )
                  .>= 1))
            )
        )
      where
        role = roomToRole room
        trueVictimCountForRoomF f = (sum (map (\victim -> oneIf (bystander victim .&& f victim)) victims)) :: SWord8
        trueVictimsForRoom = trueVictimCountForRoomF $ \_ -> sTrue
        allCulpritsF f = (sum (map (\p -> oneIf $ (culprit p .&& (f p))) people) :: SWord8)
        culpritsForRoomF f = (sum (map (\p -> oneIf $ (role p .== sCulprit .&& (f p))) people) :: SWord8)
        culpritsForRoom = culpritsForRoomF $ \_ -> sTrue
        maleCulpritsForRoom = culpritsForRoomF $ \c -> sex c .== sMan
        maleTrueVictimsForRoom = trueVictimCountForRoomF $ \victim -> sex victim .== sMan
        haveAManToKillAMan = ite (maleTrueVictimsForRoom .>= 1) (maleCulpritsForRoom .>= 1) sTrue
        vinceAppearsToBeVictim = Data.List.any (\v -> nm v == nm vince) victims
        nonWolfgangCulprits = culpritsForRoomF $ \c -> isWolfgang c .== sNotWolfgang

    {- s must be true if a bystander says it, otherwise it could be false -}
    purple p s = (bystander p) `implies` s

    {- if the inspector is a bystander, the victim is a bystander (and they better be dead)  -}
    inspectBody room inspector victim = namedConstraint (unwords [nm inspector, "inspects", nm victim]) $ purple inspector (bystander victim .&& (apparentlyDied victim .== (liftMaybe $ Just (liftRoom room))))

    pairs l =
      let unmirrored_pairs = [(x, y) | (x : ys) <- Data.List.tails l, y <- ys]
       in unmirrored_pairs <> fmap (\(x, y) -> (y, x)) unmirrored_pairs
    vouch room people = for_ (pairs people) (\(voucher, vouchee) -> namedConstraint (unwords [nm voucher, "vouches for", nm vouchee]) $ purple voucher ((roomToRole room) vouchee .== sBystander))

    culprit p = roleOne p .== sCulprit .|| roleTwo p .== sCulprit .|| roleThree p .== sCulprit
    bystander = sNot . culprit

    implies p q = ite p q sTrue
