# Project Objective

As all three of us are fans of the Hearthstone game, we became interested in trying to simulate a simplified version of the game model after learning about Forge. Simulating our favorite game is in itself a rewarding achievement. Furthermore, we hope to use this model to simulate some envisioned game scenarios, and by analyzing the outcomes (different game results due to different execution strategies), we aim to discover some general strategies that can be effectively applied in actual game matches.

However, our aspirations don't end there. Our model also aims to tackle the challenges of game balance and diversity in game modes.At the first, one of the common issue that all game need to slove is the game balance. Balance is a broad term within gaming. Specifically, the equilibrium of a game determines not only its lifespan but also its reputation and profitability. For instance, what initial state (such as health points, attack points, etc.) should we assign to each new minion in the next version of the game? When a new hero is introduced in the upcoming version of the game, what abilities/buffs should be given to the new hero without disrupting the game's balance? When it comes to profitability, could we introduce a new skin that enhances profitability without disrupting game balance? For example, could a minion using the new skin gain an additional attack point? These fundamental issues are what we can address with Slover. Therefore, Our project not only completed the simulation game goal we listed above, but also accomplished the Target goal -- Conduct balance testing on the game and furnish data to substantiate future expansions and additions to the game.

# Model Design and Visualization:


# Signatures and Predicates:

Sig represents the fundamental game component and the essential state components required to convey the game/time/progress status in the game Hearthstone.
    sig: 
        Minion :  Soldiers, commonly referred to as cards, are the primary units in the game. Each minion corresponds to a card and possesses its own set of attributes such as health, attack power, skills, and so forth.
        MinionState : Representing the state of Minion (dead, alive)
        SheildState : Certain minions are endowed with blocking skills.
        Action : Every turn, minions execute an action state.
        Boolean : True/False State
        Game : Time-stamp linkedList for tracking turn-based Game status
        GameTime : Time-stamp with dictionaries(eg. minions states at some time-stamp)
        Player : Red vs Blue
        PlayerState : Player's macro status (wins and losses, minions, heroes, etc.)
        Hero : Grant additional bonuses (such as increased life or attack) to each minion in the own camp.


Predicates represents the operational mechanism and boundary conditions of the game. In essence, 'Predicates' represents the framework of rules governing the game's operations.
    Predicates: 

    /* Need to adding an marco-explanations about what pred done and how it works */

# Testing:
The testing strategy for the project encompasses four components: Sig Properties Testing, Game Procedure Testing, LIVENESS TEST, and STARVATION FREE TEST. I will outline the purpose and function of each of these components：

    -- Sig Properties Testing :
        Establish the boundaries of the foundation. Ensure that each attribute in every sig remains consistently within the designated boundary, unaffected by changes in the game state. For example: Regarding the time-stamp sig "GameTime," we aim to prevent any timestamps from occurring prior to the initial time (T0). Furthermore, we seek to ensure that "T-end + 1" timestamps do not occur after the final state, T-end. 

    -- Game Procedure Testing : 
        Establish boundaries for each game operation. The purpose of our "test predicates" is to evaluate whether each stage of the game aligns with our design objectives. In essence, we examine whether the effects of each of the game's "behaviors" adhere to our operational constraints. For example: When Red's minion attacks Blue's minion, is the minion capable of calculating its own status (e.g., immunity, health decrease, or transition to dead status) based on the opponent's attack and its own skills? Hence, the primary function of operation testing is to verify the proper functionality of the game and to identify elements that could potentially impact the game's balance.

    -- LIVENESS TEST :
        Eventually, all games can produce a `WINNER Player` instead of going on endlessly. This test ensures that the game will eventually end.
    
    -- STARVATION FREE TEST : 
        This test consists of two parts. No player remains constantly in a state of being attacked or constantly initiating attacks. Secondly, no minion remains unchanged from the start to the end of the game.



###  What tradeoffs did you make in choosing your representation? 

### What else did you try that didn’t work as well?

### What assumptions did you make about scope? What are the limits of your model?

### Did your goals change at all from your proposal?

No, According to our initial goal setting, we have accomplished not only the simulation of the 
game but also the modeling tests of elements that could potentially influence the game's balance.

### Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

### How should we understand an instance of your model and what your visualization shows (whether custom or default)?

### Collaborators
We don't have any external collaborators outside of the team.