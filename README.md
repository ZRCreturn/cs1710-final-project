# Project Objective

Since all three of us are fans of the game Hearthstone, we're interested in simulating a simplified version after learning about Forge. Simulating our favorite game is already rewarding in itself, but we also want to use this model to explore game scenarios. By analyzing the outcomes of different strategies, we hope to uncover effective general tactics that players can apply in real matches. For beginners, our model will provide valuable insights into basic strategies that help secure victories. For seasoned players, the data-driven results will offer an advantage over relying solely on intuition.

However, our aspirations don't end there. Our model also aims to tackle the challenges of game balance and diversity in game modes. At the first, one of the common issue that all game need to slove is the game balance. Balance is a broad term within gaming. Specifically, the equilibrium of a game determines not only its lifespan but also its reputation and profitability. For instance, what initial state (such as health, attack etc.) should we assign to each new minion in the next version of the game? When a new hero is introduced in the upcoming version of the game, what abilities/buffs should be given to the new hero without disrupting the game's balance? When it comes to profitability, could we introduce a new skin that enhances profitability without disrupting game balance? These fundamental issues are what we can address with Slover. To be more specific, we can test all these things in the pre-project phase using solvers, rather than actually developing these new features and test in the internal or beta version. By doing this, game company can save a lot of development resources. Therefore, Our project not only completed the simulation game goal we listed above, but also has much practical significance

# Model Design and Visualization:
The whole game is a time sequence running through the beginning and the end of the game, and we constrain the connection relationship between the minimum time unit **GameTime** of each action through the predicate of ``traces``, and record the whole game trajectory.  Specifically, we use the ``step`` predicate to connect each pair of **GameTimes**. Within each step, two key types of actions can occur:

1. **Turn change**: Switches control to the opponent's turn.
2. **MinionAction**: Determines a minion's action, whether attacking or choosing to do nothing.



This approach allows us to accurately record and analyze the entire sequence of events throughout the game.

Our model simplifies the game by no longer focusing on the heroes and putting all the attention on minion interactions. This is because in a real game, the core means of winning is to gain an advantage over your minions. Once the follower has the lower hand, the hero can only be drained to death even if he has more blood.

Condition to win: 
1. When all of one side's followers are killed, the other side is declared the winner. 
2. above is constranined by the predicate ``winningAfter``

# Signatures and Predicates

### Signatures:

Sig Represents the fundamental game component and the essential state components required to convey the game/time/progress status in Hearthstone.

- **Minion**: Soldiers, commonly known as cards, are the primary units in the game. Each minion corresponds to a card and has its own attributes, such as health, attack power, and skills.

- **MinionState**: Represents the state of a minion (dead or alive).

- **ShieldState**: Indicates whether a minion has a shield.

- **Action**: Defines the action state executed by minions in every turn.

- **Boolean**: Represents a True/False state.

- **Game**: A linked list of timestamps used to track the turn-based game status.

- **GameTime**: A timestamp that includes dictionaries (e.g., the states of minions at a given timestamp).

- **Player**: Represents the two competing players, Red and Blue.

- **PlayerState**: Denotes the player's overall status (wins and losses, minions, heroes, etc.).

### Predicates:

Predicates represent the operational mechanisms and boundary conditions of the game. They serve as the framework of rules that govern gameplay. 

- **Init series predicates:** they are used to initialize the game, including ``InitPlayerStateSAT``, ``InitHeroStateSAT``, ``InitMinionState``, ``InitGameTime``. they are used int a general pred ``InitStateChecksSAT``

- **winningAfter:** this predicate defines the winning condition.

- **trace:** predicate recoding the game trace, also it defines the chain structure of GameTime.

- **step:** Indicates each move of the game, similar to each chess piece making a move in chess.

- **attackFrame:** helper predicate defines the framework of an attack move.

- **attack:** actual attack of a minion. Both it and attackFrame pred takes 4 peremeters. the first two indicate the attacker and the victim, they are all Minions. And the last two are Gametimes, they represent the game time before and after the execution of the action respectively.

- **turnChange:** it represents turn changes to opponent, in this pred, two things are done. First is to change the turn feild to another player. Second is to reset all of the minions' tmAction in the next GameTime to NotAction.

- **doNothing:** Another action of a minion.

- **minionAction:** indicates a minon's action. All action pred's are written in strict compliance with the Guard->action->frame principle.





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
As mentioned above, we made the trade-off of not fully modeling the entire game, but instead filtering out the most central part of the game, the minions exchange, for modeling. This is partly because it makes our model more intuitive and easier to clearly explore generic game strategies. On the other hand, it is because forges do have performance limitations, and with our current model, if the GameTime is too large, it already causes the model to run very slowly, and if we add in the hero factor, it will only get worse.


### What assumptions did you make about scope? What are the limits of your model?
We limit the number of minions to a maximum of eight, and also set a certain limit on game time, eg. limiting it to 15, which means the game lasts 3 to 4 turns. All of this is a limitation on the size of the game, as the performance of the forges is not up to the demands of a larger scale, and we don't have unique skills for each card, etc., as this is not very relevant to the core gameplay, and has significant design complexity.

### Did your goals change at all from your proposal?

No, According to our initial goal setting, we have accomplished not only the simulation of the 
game but also the modeling tests of elements that could potentially influence the game's balance.

### How should we understand an instance of your model and what your visualization shows (whether custom or default)?
// TODO by futao

### Collaborators
We don't have any external collaborators outside of the team.