#lang forge/temporal
open "hearthstone.frg"

/****************************************
* Section 1 : Init State Test           * 
****************************************/


-- 1.1 Player Init state testing 
pred test_PlayerInitialState[p : Player] {
    (p.hero = Nightmare)
    (p.pState = PlayerLive )
    (#{p.minions} = 5)
    (noSharedMinions)
    (validHeroState[p])
    (validMinionState[p])
}
pred validHeroState [p : Player]{
    all h: Hero | {
        (p.hero = h ) => {h.hHealth > 0}
    }
}
pred validMinionState[p : Player]{
    all m : Minion | {
       ( m in p.minions) implies {
            m.mAttack >= 0
            m.mHealth > 0
            m.mAction = NotAction
            m.mState = MinionLive
       }
    }
}
pred noSharedMinions{
    #{Red.minions & Blue.minions} = 0
}

-- Init Case testing

    --1.2 Minions testing
pred noUnexpectMinions {
    all m : Minion {
        always{((m = S1) or (m = S2) or (m = S3) or 
        (m = S4) or (m = S5) or (m = S6) or 
        (m = S7) or (m = S8) or (m = S9) or 
        (m = S10))}
    }
}
    --1.3 Hero state s --> s' undead checking 
pred validHero {
    always{all h : Hero {
        h.hHealth > 0
    }}
}

/****************************************
* Section 2 : State transfer test       * 
****************************************/









test expect {
    test1 : {traces implies test_PlayerInitialState[Player]} for exactly 2 Player is sat
    test2 : {traces implies noUnexpectMinions}for exactly 2 Player is sat
    test3 : {traces implies validHero} for exactly 2 Player is sat
}