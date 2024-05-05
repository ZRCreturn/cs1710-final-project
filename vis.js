let content = `${Game0.join(firstState)}`

const state_to_string = (game_time, player) => [
    `### ${game_time} ###`,
    `Turn: ${player}`
].join("\n")

const render = (game_time) => {
    const player = game_time.join(turn)
    const game_time_info = state_to_string(game_time, player)
    return game_time_info
}

const render_all = (game_time) => {
    const s = render(game_time)
    const next_game_time = game_time.join(Game0.join(next))
    
    if (next_game_time.empty()) {
        return s
    } else {
        const rest = render_all(next_game_time)
        return s + "\n" + rest
    }
}

const text = document.createElement("pre")
text.textContent = render_all(Game0.join(firstState))
div.appendChild(text)